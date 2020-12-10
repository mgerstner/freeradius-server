/*
 * files.c	Read config files into memory.
 *
 * Version:     $Id$
 *
 *   This program is free software; you can redistribute it and/or modify
 *   it under the terms of the GNU General Public License as published by
 *   the Free Software Foundation; either version 2 of the License, or
 *   (at your option) any later version.
 *
 *   This program is distributed in the hope that it will be useful,
 *   but WITHOUT ANY WARRANTY; without even the implied warranty of
 *   MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 *   GNU General Public License for more details.
 *
 *   You should have received a copy of the GNU General Public License
 *   along with this program; if not, write to the Free Software
 *   Foundation, Inc., 51 Franklin St, Fifth Floor, Boston, MA 02110-1301, USA
 *
 * @copyright 2000,2006 The FreeRADIUS server project
 * @copyright 2000 Miquel van Smoorenburg (miquels@cistron.nl)
 * @copyright 2000 Alan DeKok (aland@freeradius.org)
 */

RCSID("$Id$")

#include <freeradius-devel/server/log.h>
#include <freeradius-devel/util/debug.h>
#include <freeradius-devel/server/users_file.h>
#include <freeradius-devel/server/cond.h>

#include <freeradius-devel/util/misc.h>
#include <freeradius-devel/util/pair_legacy.h>
#include <freeradius-devel/util/syserror.h>

#include <sys/stat.h>

#include <ctype.h>
#include <fcntl.h>

/*
 *	Debug code.
 */
#if 0
static void debug_pair_list(PAIR_LIST *pl)
{
	fr_pair_t *vp;
	fr_cursor_t cursor;

	while(pl) {
		printf("Pair list: %s\n", pl->name);
		printf("** Check:\n");
		for(vp = fr_cursor_init(&cursor, &pl->check); vp; vp = fr_cursor_next(&cursor)) {
			printf("    ");
			fr_log(&default_log, L_DBG, __FILE__, __LINE__, "%pP", vp);
			printf("\n");
		}
		printf("** Reply:\n");
		for(vp = fr_cursor_init(&cursor, &pl->reply); vp; vp = fr_cursor_next(&cursor)) {
			printf("    ");
			fr_log(&default_log, L_DBG, __FILE__, __LINE__, "%pP", vp);
			printf("\n");
		}
		pl = pl->next;
	}
}
#endif

/*
 *	Free a PAIR_LIST
 */
void pairlist_free(PAIR_LIST **pl)
{
	talloc_free(*pl);
	*pl = NULL;
}

static bool const sbuff_char_space[UINT8_MAX + 1] = {
	['\t'] = true, ['\v'] = true, ['\f'] = true, [' '] = true,
};

static const fr_sbuff_term_t name_terms = FR_SBUFF_TERMS(
		L("\t"),
		L("\n"),
		L(" "),
		L("#"),
);

static fr_sbuff_parse_rules_t const rhs_term = {
	.escapes = &(fr_sbuff_unescape_rules_t){
		.chr = '\\',
		/*
		 *	Allow barewords to contain whitespace
		 *	if they're escaped.
		 */
		.subs = {
			['\t'] = '\t',
			['\n'] = '\n',
			[' '] = ' '
		},
		.do_hex = true,
		.do_oct = false
	},
	.terminals = &FR_SBUFF_TERMS(
		L("\t"),
		L("\n"),
		L(" "),
		L("#"),
		L(","),
	)
};

/*
 *	Read the users file. Return a PAIR_LIST.
 */
int pairlist_read(TALLOC_CTX *ctx, fr_dict_t const *dict, char const *file, PAIR_LIST **list, int complain)
{
	FILE *fp;
	char const *p;
	char *q;
	PAIR_LIST *pl = NULL;
	PAIR_LIST **last = &pl;
	int order = 0;
	int lineno		= 1;
	map_t			**map_tail;
	fr_sbuff_t		sbuff;
	fr_sbuff_uctx_file_t	fctx;
	tmpl_rules_t		lhs_rules, rhs_rules;
	char			buffer[8192];

	DEBUG2("Reading file %s", file);

	/*
	 *	Open the file.  The error message should be a little
	 *	more useful...
	 */
	if ((fp = fopen(file, "r")) == NULL) {
		if (!complain) return -1;

		ERROR("Couldn't open %s for reading: %s", file, fr_syserror(errno));
		return -1;
	}

	fr_sbuff_init_file(&sbuff, &fctx, buffer, sizeof(buffer), fp, SIZE_MAX);

	lhs_rules = (tmpl_rules_t) {
		.dict_def = dict,
		.request_def = REQUEST_CURRENT,
		.prefix = TMPL_ATTR_REF_PREFIX_AUTO,
		.disallow_qualifiers = true, /* for now, until more tests are made */
		.allow_unresolved = true,
	};
	rhs_rules = (tmpl_rules_t) {
		.dict_def = dict,
		.request_def = REQUEST_CURRENT,
		.prefix = TMPL_ATTR_REF_PREFIX_YES,
		.disallow_qualifiers = true, /* for now, until more tests are made */
		.skip_autoparse = true,
	};

	while (true) {
		unsigned char	c;
		size_t		len;
		bool		comma;
		bool		leading_spaces;
		PAIR_LIST	*t;

		fprintf(stderr, "Entry %.60s\n", fr_sbuff_current(&sbuff));

		/*
		 *	If the line is empty or has only comments,
		 *	then we don't care about leading spaces.
		 */
		leading_spaces = (fr_sbuff_adv_past_allowed(&sbuff, SIZE_MAX, sbuff_char_space) > 0);
		if (fr_sbuff_next_if_char(&sbuff, '#')) {
			(void) fr_sbuff_adv_to_chr(&sbuff, SIZE_MAX, '\n');
		}
		if (fr_sbuff_next_if_char(&sbuff, '\n')) {
			lineno++;
			continue;
		}

		/*
		 *	We're trying to read a name.  It MUST have
		 *	been at the start of the line.  So whatever
		 *	this is, it's wrong.
		 */
		if (leading_spaces) {
			ERROR("%s[%d]: Entry does not begin with a user name",
			      file, lineno);
		fail:
			pairlist_free(&pl);
			fclose(fp);
			return -1;
		}

		/*
		 *	$INCLUDE filename
		 */
		if (fr_sbuff_is_str(&sbuff, "$INCLUDE", 8)) {
			char *newfile;
			fr_sbuff_marker_t name;

			fprintf(stderr, "INCLUDE %.60s\n", fr_sbuff_current(&sbuff));

			fr_sbuff_advance(&sbuff, 8);

			/*
			 *	Skip spaces after the $INCLUDE.
			 */
			if (fr_sbuff_adv_past_allowed(&sbuff, SIZE_MAX, sbuff_char_space) == 0) {
				ERROR("%s[%d]: Unexpected text after $INCLUDE",
				      file, lineno);
				goto fail;
			}

			/*
			 *	Remember when the name started, and
			 *	skip over the name until spaces, comments, or LF
			 */
			fr_sbuff_marker(&name, &sbuff);
			len = fr_sbuff_adv_until(&sbuff, SIZE_MAX, &name_terms, 0);
			if (len == 0) {
				fr_sbuff_marker_release(&name);
				ERROR("%s[%d]: No filename after $INCLUDE ",
				      file, lineno);
				goto fail;
			}

			/*
			 *	If the input file is a relative path,
			 *	try to copy the leading directory from
			 *	it.  If there's no leading directory,
			 *	just use the $INCLUDE name as-is.
			 *
			 *	If there is a leading directory in the
			 *	input name, paste that as the
			 *	directory to the $INCLUDE name.
			 *
			 *	Otherwise the $INCLUDE name is an
			 *	absolute path, use it as -is.
			 */
			c = *fr_sbuff_current(&name);
			if (c != '/') {
				p = strrchr(file, '/');

				if (!p) goto copy_name;

				newfile = talloc_asprintf(NULL, "%.*s/%.*s",
							  (int) (p - file), file,
							  (int) len, fr_sbuff_current(&name));
			} else {
			copy_name:
				newfile = talloc_asprintf(NULL, "%.*s", (int) len, fr_sbuff_current(&name));
			}
			fr_sbuff_marker_release(&name);

			/*
			 *	Skip spaces and comments after the name.
			 */
			fr_sbuff_adv_past_allowed(&sbuff, SIZE_MAX, sbuff_char_space);
			if (fr_sbuff_next_if_char(&sbuff, '#')) {
				(void) fr_sbuff_adv_to_chr(&sbuff, SIZE_MAX, '\n');
			}

			/*
			 *	There's no LF, but if we skip
			 *	non-spaces and non-comments to find
			 *	the LF, then there must be extra text
			 *	after the filename.  That's an error.
			 */
			if (!fr_sbuff_is_char(&sbuff, '\n') &&
			    (fr_sbuff_adv_to_chr(&sbuff, SIZE_MAX, '\n') > 0)) {
				ERROR("%s[%d]: Unexpected text after filename",
				      file, lineno);
				talloc_free(newfile);
				goto fail;
			}

			/*
			 *	Read the $INCLUDEd file recursively.
			 */
			if (pairlist_read(ctx, dict, newfile, last, 0) != 0) {
				ERROR("%s[%d]: Could not read included file %s: %s",
				      file, lineno, newfile, fr_syserror(errno));
				talloc_free(newfile);
				goto fail;
			}
			talloc_free(newfile);

			/*
			 *	The file may have read no entries, one
			 *	entry, or it may be a linked list of
			 *	entries.  Go to the end of the list.
			 */
			while (*last) {
				(*last)->order = order++;
				last = &((*last)->next);
			}

			/*
			 *	Go to the next line.
			 */
			if (fr_sbuff_next_if_char(&sbuff, '\n')) {
				lineno++;
				continue;
			}

			/*
			 *	The next character is not LF, but we
			 *	skipped to LF above.  So, by process
			 *	of elimination, we must be at EOF.
			 */
			break;
		} /* else it wasn't $INCLUDE */

		/*
		 *	We MUST be either at a valid entry, OR at EOF.
		 */
		MEM(t = talloc_zero(ctx, PAIR_LIST));
		t->lineno = lineno;
		t->order = order++;

		/*
		 *	Copy the name from the entry.
		 */
		len = fr_sbuff_out_abstrncpy_until(t, &q, &sbuff, SIZE_MAX, &name_terms, NULL);
		if (len == 0) {
			talloc_free(t);
			break;
		}
		t->name = q;
		map_tail = &t->check;

		lhs_rules.list_def = PAIR_LIST_CONTROL;
		comma = false;

		fprintf(stderr, "ALLOC %s %.60s\n", t->name, fr_sbuff_current(&sbuff));

check_item:
		fprintf(stderr, "CHECK %.60s\n", fr_sbuff_current(&sbuff));

		/*
		 *	Skip spaces before the item, and allow the
		 *	check list to end on comment or LF.
		 */
		(void) fr_sbuff_adv_past_allowed(&sbuff, SIZE_MAX, sbuff_char_space);
		if (fr_sbuff_is_char(&sbuff, '#')) goto check_item_comment;
		if (fr_sbuff_is_char(&sbuff, '\n')) goto check_item_end;

		/*
		 *	Try to parse the check item.
		 */
		fprintf(stderr, "MAP CHECK %.60s\n", fr_sbuff_current(&sbuff));
		if (map_afrom_sbuff(t, map_tail, &sbuff, cond_cmp_op_table, cond_cmp_op_table_len,
				    &lhs_rules, &rhs_rules, &rhs_term) < 0) {
			ERROR("%s[%d]: Failed reading check pair: %s",
			      file, lineno, fr_strerror());
		fail_entry:
			talloc_free(t);
			goto fail;
		}

		/*
		 *	The map "succeeded", but no map was created.
		 *	It must have hit a terminal character, OR EOF.
		 *
		 *	Except we've already skipped spaces, tabs,
		 *	comments, and LFs.  So the only thing which is
		 *	left is a comma.
		 */
		if (!*map_tail) {
			fprintf(stderr, "no map!\n");
			if (fr_sbuff_is_char(&sbuff, ',')) {
				ERROR("%s[%d]: Unexpected extra comma reading check pair",
				      file, lineno);
				goto fail_entry;
			}

			/*
			 *	Otherwise map_afrom_sbuff() returned
			 *	nothing, because there's no more
			 *	input.
			 */

		add_entry:
			return -1;


			*last = t;
			break;
		}
		fr_assert((*map_tail)->lhs != NULL);

		if (!tmpl_is_attr((*map_tail)->lhs)) {
			ERROR("%s[%d]: Unknown attribute '%s'",
			      file, lineno, (*map_tail)->lhs->name);
			goto fail_entry;
		}

		fr_assert((*map_tail)->rhs != NULL);
		fr_assert(!tmpl_is_attr((*map_tail)->rhs));
		fr_assert((*map_tail)->next == NULL);

		/*
		 *	There can be spaces before any comma.
		 */
		(void) fr_sbuff_adv_past_allowed(&sbuff, SIZE_MAX, sbuff_char_space);

		/*
		 *	Allow a comma after this item.  But remember
		 *	if we had a comma.
		 */
		if (fr_sbuff_next_if_char(&sbuff, ',')) {
			comma = true;
			map_tail = &(*map_tail)->next;
			goto check_item;
		}
		comma = false;

	check_item_comment:
		/*
		 *	There wasn't a comma after the item, so the
		 *	next thing MUST be a comment, LF, EOF.
		 *
		 *	If there IS stuff before the LF, then it's
		 *	unknown text.
		 */
		if (fr_sbuff_next_if_char(&sbuff, '#')) {
			fprintf(stderr, "SKIP COMMENT\n");
			(void) fr_sbuff_adv_to_chr(&sbuff, SIZE_MAX, '\n');
		}
	check_item_end:
		fprintf(stderr, "CHECK LIST END %.60s\n", fr_sbuff_current(&sbuff));
		if (fr_sbuff_next_if_char(&sbuff, '\n')) {
			/*
			 *	The check item list ended with a comma.
			 *	That's bad.
			 */
			if (comma) {
				ERROR("%s[%d]: Invalid comma ending the check item list.",
				      file, lineno);
				goto fail_entry;
			}

			lineno++;
			goto setup_reply;
		}

#if 0
		(fr_sbuff_adv_to_chr(&sbuff, SIZE_MAX, '\n') > 0)) {
			ERROR("%s[%d]: Unexpected text after check items: %s",
			      file, lineno, fr_strerror());
			goto fail_entry;
		}


		/*
		 *	The next character is not LF, but we
		 *	skipped to LF above.  So, by process
		 *	of elimination, we must be at EOF.
		 */
		if (!fr_sbuff_is_char(&sbuff, '\n')) {
			fprintf(stderr, "ADD %d\n", __LINE__);
			goto add_entry;
		}
#endif

setup_reply:
		fprintf(stderr, "START REPLY\n");

		/*
		 *	Setup the reply items.
		 */
		map_tail = &t->reply;
		lhs_rules.list_def = PAIR_LIST_CONTROL;
		comma = false;

reply_item:
		fprintf(stderr, "REPLY %.60s\n", fr_sbuff_current(&sbuff));

		/*
		 *	Reply items start with spaces.  If there's no
		 *	spaces, then the current entry is done.  Add
		 *	it to the list, and go back to reading the
		 *	user name or $INCLUDE.
		 */
		if (fr_sbuff_adv_past_allowed(&sbuff, SIZE_MAX, sbuff_char_space) == 0) {
			fprintf(stderr, "no spaces?\n");
			if (comma) {
				ERROR("%s[%d]: Unexpected trailing comma in previous line",
				      file, lineno);
				goto fail_entry;
			}

			/*
			 *	The line doesn't begin with spaces.
			 *	The list of reply items MUST be
			 *	finished.  Go look for an entry name.
			 *
			 *	Note that we don't allow comments in
			 *	the middle of the reply item list.  Oh
			 *	well.
			 */
			*last = t;
			last = &(t->next);
			continue;

		} else if (lineno == (t->lineno + 1)) {
			fr_assert(comma == false);

		} else if (!comma) {
			ERROR("%s[%d]: Missing comma in previous line",
			      file, lineno);
			goto fail_entry;
		}

next_reply_item:
		fprintf(stderr, "REPLY NEXT %.60s\n", fr_sbuff_current(&sbuff));

		/*
		 *	Unlike check items, we don't skip spaces or
		 *	comments here.
		 */
		if (map_afrom_sbuff(t, map_tail, &sbuff, map_assignment_op_table, map_assignment_op_table_len,
				    &lhs_rules, &rhs_rules, &rhs_term) < 0) {
			ERROR("%s[%d]: Failed reading reply pair: %s",
			      file, lineno, fr_strerror());
			goto fail;
		}
		fprintf(stderr, "MAP SUCCEEDED WITH %p\n", *map_tail);

		/*
		 *	The map "succeeded", but no map was created.
		 *	Maybe we hit a terminal string, or EOF.
		 *
		 *	We can't have hit space/tab, as that was
		 *	checked for at "reply_item", and again after
		 *	map_afrom_sbuff(), if we actually got
		 *	something.
		 *
		 *	What's left is a comment, comma, LF, or EOF.
		 */
		if (!*map_tail) {
			(void) fr_sbuff_adv_past_allowed(&sbuff, SIZE_MAX, sbuff_char_space);
			if (fr_sbuff_is_char(&sbuff, ',')) {
				ERROR("%s[%d]: Unexpected extra comma reading reply pair",
				      file, lineno);
				goto fail_entry;
			}

			if (fr_sbuff_next_if_char(&sbuff, '#')) goto reply_item_comment;
			if (fr_sbuff_next_if_char(&sbuff, '\n')) goto reply_item_end;

			/*
			 *	We didn't read anything, but none of
			 *	the terminal characters match.  It must be EOF.
			 */
			goto add_entry;
		}
		fr_assert((*map_tail)->lhs != NULL);
		if (!tmpl_is_attr((*map_tail)->lhs)) {
			ERROR("%s[%d]: Unknown attribute '%s'",
			      file, lineno, (*map_tail)->lhs->name);
			goto fail_entry;
		}

		fr_assert((*map_tail)->rhs != NULL);
		fr_assert(!tmpl_is_attr((*map_tail)->rhs));
		fr_assert((*map_tail)->next == NULL);

		map_tail = &(*map_tail)->next;

		(void) fr_sbuff_adv_past_allowed(&sbuff, SIZE_MAX, sbuff_char_space);

		/*
		 *	Commas separate entries on the same line.  And
		 *	we allow spaces after commas, too.
		 */
		if (fr_sbuff_next_if_char(&sbuff, ',')) {
			comma = true;
			(void) fr_sbuff_adv_past_allowed(&sbuff, SIZE_MAX, sbuff_char_space);
		} else {
			comma = false;
		}

		/*
		 *	Comments or LF will end this particular line.
		 *
		 *	Reading the next line will cause a complaint
		 *	if this line ended with a comma.
		 */
	reply_item_comment:
		if (fr_sbuff_next_if_char(&sbuff, '#')) {
			(void) fr_sbuff_adv_to_chr(&sbuff, SIZE_MAX, '\n');
		}
	reply_item_end:
		if (fr_sbuff_next_if_char(&sbuff, '\n')) {
			lineno++;
			goto reply_item;
		}

		/*
		 *	Not comment or LF, the content MUST be another
		 *	pair.
		 */
		if (comma) goto next_reply_item;

		ERROR("%s[%d]: Unexpected text after reply pair: %s",
		      file, lineno, fr_sbuff_current(&sbuff));
		goto fail_entry;
	}

	/*
	 *	Else we were looking for an entry.  We didn't get one
	 *	because we were at EOF, so that's OK.
	 */

	fclose(fp);

	*list = pl;
	return 0;
}
