/*
 *   This program is is free software; you can redistribute it and/or modify
 *   it under the terms of the GNU General Public License, version 2 if the
 *   License as published by the Free Software Foundation.
 *
 *   This program is distributed in the hope that it will be useful,
 *   but WITHOUT ANY WARRANTY; without even the implied warranty of
 *   MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 *   GNU General Public License for more details.
 *
 *   You should have received a copy of the GNU General Public License
 *   along with this program; if not, write to the Free Software
 *   Foundation, Inc., 51 Franklin St, Fifth Floor, Boston, MA 02110-1301, USA
 */

/**
 * $Id$
 * @file rlm_sql.c
 * @brief Implements SQL 'users' file, and SQL accounting.
 *
 * @copyright 2012  Arran Cudbard-Bell <a.cudbardb@freeradius.org>
 * @copyright 2000,2006  The FreeRADIUS server project
 * @copyright 2000  Mike Machado <mike@innercite.com>
 * @copyright 2000  Alan DeKok <aland@ox.org>
 */
#include <freeradius-devel/ident.h>
RCSID("$Id$")

#include <ctype.h>

#include <freeradius-devel/radiusd.h>
#include <freeradius-devel/modules.h>
#include <freeradius-devel/token.h>
#include <freeradius-devel/rad_assert.h>

#include <sys/stat.h>

#include "rlm_sql.h"

static const CONF_PARSER acct_section_config[] = {
	{"reference", PW_TYPE_STRING_PTR,
	  offsetof(sql_acct_section_t, reference), NULL, ".query"},
	{"logfile", PW_TYPE_STRING_PTR,
	 offsetof(sql_acct_section_t, logfile), NULL, NULL},
	
	{NULL, -1, 0, NULL, NULL}
};

static const CONF_PARSER module_config[] = {
	{"driver", PW_TYPE_STRING_PTR,
	 offsetof(rlm_sql_config_t,sql_driver_name), NULL, "rlm_sql_null"},
	{"server", PW_TYPE_STRING_PTR,
	 offsetof(rlm_sql_config_t,sql_server), NULL, "localhost"},
	{"port", PW_TYPE_STRING_PTR,
	 offsetof(rlm_sql_config_t,sql_port), NULL, ""},
	{"login", PW_TYPE_STRING_PTR,
	 offsetof(rlm_sql_config_t,sql_login), NULL, ""},
	{"password", PW_TYPE_STRING_PTR,
	 offsetof(rlm_sql_config_t,sql_password), NULL, ""},
	{"radius_db", PW_TYPE_STRING_PTR,
	 offsetof(rlm_sql_config_t,sql_db), NULL, "radius"},
	{"read_groups", PW_TYPE_BOOLEAN,
	 offsetof(rlm_sql_config_t,read_groups), NULL, "yes"},
	{"readclients", PW_TYPE_BOOLEAN,
	 offsetof(rlm_sql_config_t,do_clients), NULL, "no"},
	{"deletestalesessions", PW_TYPE_BOOLEAN,
	 offsetof(rlm_sql_config_t,deletestalesessions), NULL, "yes"},
	{"sql_user_name", PW_TYPE_STRING_PTR,
	 offsetof(rlm_sql_config_t,query_user), NULL, ""},
	{"logfile", PW_TYPE_STRING_PTR,
	 offsetof(rlm_sql_config_t,logfile), NULL, NULL},
	{"default_user_profile", PW_TYPE_STRING_PTR,
	 offsetof(rlm_sql_config_t,default_profile), NULL, ""},
	{"nas_query", PW_TYPE_STRING_PTR,
	 offsetof(rlm_sql_config_t,nas_query), NULL,
	 "SELECT id,nasname,shortname,type,secret FROM nas"},
	{"authorize_check_query", PW_TYPE_STRING_PTR,
	 offsetof(rlm_sql_config_t,authorize_check_query), NULL, ""},
	{"authorize_reply_query", PW_TYPE_STRING_PTR,
	 offsetof(rlm_sql_config_t,authorize_reply_query), NULL, NULL},
	{"authorize_group_check_query", PW_TYPE_STRING_PTR,
	 offsetof(rlm_sql_config_t,authorize_group_check_query), NULL, ""},
	{"authorize_group_reply_query", PW_TYPE_STRING_PTR,
	 offsetof(rlm_sql_config_t,authorize_group_reply_query), NULL, ""},
	{"group_membership_query", PW_TYPE_STRING_PTR,
	 offsetof(rlm_sql_config_t,groupmemb_query), NULL, NULL},
#ifdef WITH_SESSION_MGMT
	{"simul_count_query", PW_TYPE_STRING_PTR,
	 offsetof(rlm_sql_config_t,simul_count_query), NULL, ""},
	{"simul_verify_query", PW_TYPE_STRING_PTR,
	 offsetof(rlm_sql_config_t,simul_verify_query), NULL, ""},
#endif
	{"safe-characters", PW_TYPE_STRING_PTR,
	 offsetof(rlm_sql_config_t,allowed_chars), NULL,
	"@abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ0123456789.-_: /"},

	/*
	 *	This only works for a few drivers.
	 */
	{"query_timeout", PW_TYPE_INTEGER,
	 offsetof(rlm_sql_config_t,query_timeout), NULL, NULL},
	
	{NULL, -1, 0, NULL, NULL}
};

/*
 *	Fall-Through checking function from rlm_files.c
 */
static int fallthrough(VALUE_PAIR *vp)
{
	VALUE_PAIR *tmp;
	tmp = pairfind(vp, PW_FALL_THROUGH, 0, TAG_ANY);

	return tmp ? tmp->vp_integer : 0;
}

/*
 *	Yucky prototype.
 */
static int generate_sql_clients(rlm_sql_t *inst);
static size_t sql_escape_func(REQUEST *, char *out, size_t outlen, const char *in, void *arg);

/*
 *			SQL xlat function
 *
 *  For selects the first value of the first column will be returned,
 *  for inserts, updates and deletes the number of rows afftected will be
 *  returned instead.
 */
static size_t sql_xlat(void *instance, REQUEST *request,
		    const char *fmt, char *out, size_t freespace)
{
	rlm_sql_handle_t *handle;
	rlm_sql_row_t row;
	rlm_sql_t *inst = instance;
	char querystr[MAX_QUERY_LEN];
	size_t ret = 0;

	RDEBUG("sql_xlat");

	/*
	 * Add SQL-User-Name attribute just in case it is needed
	 *  We could search the string fmt for SQL-User-Name to see if this is
	 *  needed or not
	 */
	sql_set_user(inst, request, NULL);
	/*
	 * Do an xlat on the provided string (nice recursive operation).
	 */
	if (!radius_xlat(querystr, sizeof(querystr), fmt, request, sql_escape_func, inst)) {
		radlog(L_ERR, "rlm_sql (%s): xlat failed.",
		       inst->config->xlat_name);
		return 0;
	}

	handle = sql_get_socket(inst);
	if (handle == NULL)
		return 0;

	rlm_sql_query_log(inst, request, NULL, querystr);

	/*
	 *	If the query starts with any of the following prefixes,
	 *	then return the number of rows affected
	 */
	if ((strncasecmp(querystr, "insert", 6) == 0) ||
	    (strncasecmp(querystr, "update", 6) == 0) ||
	    (strncasecmp(querystr, "delete", 6) == 0)) {
		int numaffected;
		char buffer[21]; /* 64bit max is 20 decimal chars + null byte */

		if (rlm_sql_query(&handle,inst,querystr)) {
			sql_release_socket(inst,handle);
			
			return 0;
		}
	
		numaffected = (inst->module->sql_affected_rows)(handle,
								inst->config);
		if (numaffected < 1) {
			RDEBUG("rlm_sql (%s): SQL query affected no rows",
				inst->config->xlat_name);
		}

		/*
		 *	Don't chop the returned number if freespace is
		 *	too small.  This hack is necessary because
		 *	some implementations of snprintf return the
		 *	size of the written data, and others return
		 *	the size of the data they *would* have written
		 *	if the output buffer was large enough.
		 */
		snprintf(buffer, sizeof(buffer), "%d", numaffected);
		ret = strlen(buffer);
		if (ret >= freespace){
			RDEBUG("rlm_sql (%s): Can't write result, insufficient string space",
			       inst->config->xlat_name);
			(inst->module->sql_finish_query)(handle,
							 inst->config);
			sql_release_socket(inst,handle);
			return 0;
		}
		
		memcpy(out, buffer, ret + 1); /* we did bounds checking above */

		(inst->module->sql_finish_query)(handle, inst->config);
		sql_release_socket(inst,handle);
		return ret;
	} /* else it's a SELECT statement */

	if (rlm_sql_select_query(&handle,inst,querystr)){
		sql_release_socket(inst,handle);
		return 0;
	}

	ret = rlm_sql_fetch_row(&handle, inst);
	if (ret) {
		RDEBUG("SQL query did not succeed");
		(inst->module->sql_finish_select_query)(handle, inst->config);
		sql_release_socket(inst,handle);
		return 0;
	}

	row = handle->row;
	if (row == NULL) {
		RDEBUG("SQL query did not return any results");
		(inst->module->sql_finish_select_query)(handle, inst->config);
		sql_release_socket(inst,handle);
		return 0;
	}

	if (row[0] == NULL){
		RDEBUG("Null value in first column");
		(inst->module->sql_finish_select_query)(handle, inst->config);
		sql_release_socket(inst,handle);
		return 0;
	}
	ret = strlen(row[0]);
	if (ret >= freespace){
		RDEBUG("Insufficient string space");
		(inst->module->sql_finish_select_query)(handle, inst->config);
		sql_release_socket(inst,handle);
		return 0;
	}

	strlcpy(out,row[0],freespace);

	RDEBUG("sql_xlat finished");

	(inst->module->sql_finish_select_query)(handle, inst->config);
	sql_release_socket(inst,handle);
	return ret;
}

static int generate_sql_clients(rlm_sql_t *inst)
{
	rlm_sql_handle_t *handle;
	rlm_sql_row_t row;
	char querystr[MAX_QUERY_LEN];
	RADCLIENT *c;
	char *prefix_ptr = NULL;
	unsigned int i = 0;
	int numf = 0;

	DEBUG("rlm_sql (%s): Processing generate_sql_clients",
	      inst->config->xlat_name);

	/* NAS query isn't xlat'ed */
	strlcpy(querystr, inst->config->nas_query, sizeof(querystr));
	DEBUG("rlm_sql (%s) in generate_sql_clients: query is %s",
	      inst->config->xlat_name, querystr);

	handle = sql_get_socket(inst);
	if (handle == NULL)
		return -1;
	if (rlm_sql_select_query(&handle,inst,querystr)){
		return -1;
	}

	while(rlm_sql_fetch_row(&handle, inst) == 0) {
		i++;
		row = handle->row;
		if (row == NULL)
			break;
		/*
		 *  The return data for each row MUST be in the following order:
		 *
		 *  0. Row ID (currently unused)
		 *  1. Name (or IP address)
		 *  2. Shortname
		 *  3. Type
		 *  4. Secret
		 *  5. Virtual Server (optional)
		 */
		if (!row[0]){
			radlog(L_ERR, "rlm_sql (%s): No row id found on pass %d",inst->config->xlat_name,i);
			continue;
		}
		if (!row[1]){
			radlog(L_ERR, "rlm_sql (%s): No nasname found for row %s",inst->config->xlat_name,row[0]);
			continue;
		}
		if (!row[2]){
			radlog(L_ERR, "rlm_sql (%s): No short name found for row %s",inst->config->xlat_name,row[0]);
			continue;
		}
		if (!row[4]){
			radlog(L_ERR, "rlm_sql (%s): No secret found for row %s",inst->config->xlat_name,row[0]);
			continue;
		}

		DEBUG("rlm_sql (%s): Read entry nasname=%s,shortname=%s,secret=%s",inst->config->xlat_name,
			row[1],row[2],row[4]);

		c = talloc_zero(inst, RADCLIENT);

#ifdef WITH_DYNAMIC_CLIENTS
		c->dynamic = 1;
#endif

		/*
		 *	Look for prefixes
		 */
		c->prefix = -1;
		prefix_ptr = strchr(row[1], '/');
		if (prefix_ptr) {
			c->prefix = atoi(prefix_ptr + 1);
			if ((c->prefix < 0) || (c->prefix > 128)) {
				radlog(L_ERR, "rlm_sql (%s): Invalid Prefix value '%s' for IP.",
				       inst->config->xlat_name, prefix_ptr + 1);
				talloc_free(c);
				continue;
			}
			/* Replace '/' with '\0' */
			*prefix_ptr = '\0';
		}

		/*
		 *	Always get the numeric representation of IP
		 */
		if (ip_hton(row[1], AF_UNSPEC, &c->ipaddr) < 0) {
			radlog(L_ERR, "rlm_sql (%s): Failed to look up hostname %s: %s",
			       inst->config->xlat_name,
			       row[1], fr_strerror());
			talloc_free(c);
			continue;
		} else {
			char buffer[256];
			ip_ntoh(&c->ipaddr, buffer, sizeof(buffer));
			c->longname = talloc_strdup(c, buffer);
		}

		if (c->prefix < 0) switch (c->ipaddr.af) {
		case AF_INET:
			c->prefix = 32;
			break;
		case AF_INET6:
			c->prefix = 128;
			break;
		default:
			break;
		}

		/*
		 *	Other values (secret, shortname, nastype, virtual_server)
		 */
		c->secret = talloc_strdup(c, row[4]);
		c->shortname = talloc_strdup(c, row[2]);
		if(row[3] != NULL)
			c->nastype = strdup(row[3]);

		numf = (inst->module->sql_num_fields)(handle, inst->config);
		if ((numf > 5) && (row[5] != NULL) && *row[5]) c->server = strdup(row[5]);

		DEBUG("rlm_sql (%s): Adding client %s (%s, server=%s) to clients list",
		      inst->config->xlat_name,
		      c->longname,c->shortname, c->server ? c->server : "<none>");
		if (!client_add(NULL, c)) {
			sql_release_socket(inst, handle);
			DEBUG("rlm_sql (%s): Failed to add client %s (%s) to clients list.  Maybe there's a duplicate?",
			      inst->config->xlat_name,
			      c->longname,c->shortname);
			client_free(c);
			return -1;
		}
	}
	(inst->module->sql_finish_select_query)(handle, inst->config);
	sql_release_socket(inst, handle);

	return 0;
}


/*
 *	Translate the SQL queries.
 */
static size_t sql_escape_func(UNUSED REQUEST *request, char *out, size_t outlen,
			      const char *in, void *arg)
{
	rlm_sql_t *inst = arg;
	size_t len = 0;

	while (in[0]) {
		/*
		 *	Non-printable characters get replaced with their
		 *	mime-encoded equivalents.
		 */
		if ((in[0] < 32) ||
		    strchr(inst->config->allowed_chars, *in) == NULL) {
			/*
			 *	Only 3 or less bytes available.
			 */
			if (outlen <= 3) {
				break;
			}

			snprintf(out, outlen, "=%02X", (unsigned char) in[0]);
			in++;
			out += 3;
			outlen -= 3;
			len += 3;
			continue;
		}

		/*
		 *	Only one byte left.
		 */
		if (outlen <= 1) {
			break;
		}

		/*
		 *	Allowed character.
		 */
		*out = *in;
		out++;
		in++;
		outlen--;
		len++;
	}
	*out = '\0';
	return len;
}

/*
 *	Set the SQL user name.
 *
 *	We don't call the escape function here. The resulting string
 *	will be escaped later in the queries xlat so we don't need to
 *	escape it twice. (it will make things wrong if we have an
 *	escape candidate character in the username)
 */
int sql_set_user(rlm_sql_t *inst, REQUEST *request, const char *username)
{
	char buffer[254];
	VALUE_PAIR *vp = NULL;
	const char *sqluser;
	size_t len;

	if (username != NULL) {
		sqluser = username;
	} else if (*inst->config->query_user) {
		sqluser = inst->config->query_user;
	} else {
		return 0;
	}
	
	len = radius_xlat(buffer, sizeof(buffer), sqluser, request, NULL, NULL);
	if (!len) {
		return -1;
	}
	
	vp = pairalloc(NULL, inst->sql_user);
	vp->op = T_OP_SET;
	
	strlcpy(vp->vp_strvalue, buffer, sizeof(vp->vp_strvalue));
	vp->length = strlen(vp->vp_strvalue);
	pairadd(&request->packet->vps, vp);

	RDEBUG2("SQL-User-Name updated");

	return 0;
}


static int sql_get_grouplist(rlm_sql_t *inst, rlm_sql_handle_t *handle,
			     REQUEST *request, rlm_sql_grouplist_t **phead)
{
	char    querystr[MAX_QUERY_LEN];
	int     num_groups = 0;
	rlm_sql_row_t row;
	rlm_sql_grouplist_t *entry;

	/* NOTE: sql_set_user should have been run before calling this function */

	entry = *phead = NULL;

	if (!inst->config->groupmemb_query ||
	    (inst->config->groupmemb_query[0] == 0))
		return 0;

	if (!radius_xlat(querystr, sizeof(querystr), inst->config->groupmemb_query, request, sql_escape_func, inst)) {
		radlog_request(L_ERR, 0, request, "xlat \"%s\" failed.",
			       inst->config->groupmemb_query);
		return -1;
	}

	if (rlm_sql_select_query(&handle, inst, querystr) < 0) {
		return -1;
	}
	while (rlm_sql_fetch_row(&handle, inst) == 0) {
		row = handle->row;
		if (row == NULL)
			break;
		if (row[0] == NULL){
			RDEBUG("row[0] returned NULL");
			(inst->module->sql_finish_select_query)(handle, inst->config);
			talloc_free(entry);
			return -1;
		}

		if (!*phead) {
			*phead = talloc_zero(handle, rlm_sql_grouplist_t);
			entry = *phead;
		} else {
			entry->next = talloc_zero(*phead, rlm_sql_grouplist_t);
			entry = entry->next;
		}
		entry->next = NULL;
		strlcpy(entry->name, row[0], MAX_STRING_LEN);
	}

	(inst->module->sql_finish_select_query)(handle, inst->config);

	return num_groups;
}


/*
 * sql groupcmp function. That way we can do group comparisons (in the users file for example)
 * with the group memberships reciding in sql
 * The group membership query should only return one element which is the username. The returned
 * username will then be checked with the passed check string.
 */

static int sql_groupcmp(void *instance, REQUEST *request, VALUE_PAIR *request_vp, VALUE_PAIR *check,
			VALUE_PAIR *check_pairs, VALUE_PAIR **reply_pairs)
{
	rlm_sql_handle_t *handle;
	rlm_sql_t *inst = instance;
	rlm_sql_grouplist_t *head, *entry;

	check_pairs = check_pairs;
	reply_pairs = reply_pairs;
	request_vp = request_vp;

	RDEBUG("sql_groupcmp");
	if (!check || !check->length){
		RDEBUG("sql_groupcmp: Illegal group name");
		return 1;
	}
	if (!request){
		RDEBUG("sql_groupcmp: NULL request");
		return 1;
	}
	/*
	 *	Set, escape, and check the user attr here
	 */
	if (sql_set_user(inst, request, NULL) < 0)
		return 1;

	/*
	 *	Get a socket for this lookup
	 */
	handle = sql_get_socket(inst);
	if (handle == NULL) {
		return 1;
	}

	/*
	 *	Get the list of groups this user is a member of
	 */
	if (sql_get_grouplist(inst, handle, request, &head) < 0) {
		radlog_request(L_ERR, 0, request,
			       "Error getting group membership");
		sql_release_socket(inst, handle);
		return 1;
	}

	for (entry = head; entry != NULL; entry = entry->next) {
		if (strcmp(entry->name, check->vp_strvalue) == 0){
			RDEBUG("sql_groupcmp finished: User is a member of group %s",
			       check->vp_strvalue);
			talloc_free(head);
			sql_release_socket(inst, handle);
			return 0;
		}
	}

	/* Free the grouplist */
	talloc_free(head);
	sql_release_socket(inst,handle);

	RDEBUG("sql_groupcmp finished: User is NOT a member of group %s",
	       check->vp_strvalue);

	return 1;
}



static int rlm_sql_process_groups(rlm_sql_t *inst, REQUEST *request, rlm_sql_handle_t *handle, int *dofallthrough)
{
	VALUE_PAIR *check_tmp = NULL;
	VALUE_PAIR *reply_tmp = NULL;
	rlm_sql_grouplist_t *head, *entry;
	VALUE_PAIR *sql_group = NULL;
	char    querystr[MAX_QUERY_LEN];
	int found = 0;
	int rows;

	/*
	 *	Get the list of groups this user is a member of
	 */
	if (sql_get_grouplist(inst, handle, request, &head) < 0) {
		radlog_request(L_ERR, 0, request, "Error retrieving group list");
		return -1;
	}

	for (entry = head; entry != NULL && *dofallthrough != 0; entry = entry->next) {
		/*
		 *	Add the Sql-Group attribute to the request list so we know
		 *	which group we're retrieving attributes for
		 */
		sql_group = pairmake_packet("Sql-Group", entry->name, T_OP_EQ);
		if (!sql_group) {
			radlog_request(L_ERR, 0, request,
				       "Error creating Sql-Group attribute");
			talloc_free(head);
			return -1;
		}
		if (!radius_xlat(querystr, sizeof(querystr), inst->config->authorize_group_check_query, request, sql_escape_func, inst)) {
			radlog_request(L_ERR, 0, request,
				       "Error generating query; rejecting user");
			/* Remove the grouup we added above */
			pairdelete(&request->packet->vps, PW_SQL_GROUP, 0, TAG_ANY);
			talloc_free(head);
			return -1;
		}
		rows = sql_getvpdata(inst, &handle, request, &check_tmp, querystr);
		if (rows < 0) {
			radlog_request(L_ERR, 0, request, "Error retrieving check pairs for group %s",
			       entry->name);
			/* Remove the grouup we added above */
			pairdelete(&request->packet->vps, PW_SQL_GROUP, 0, TAG_ANY);
			pairfree(&check_tmp);
			talloc_free(head);
			return -1;
		} else if (rows > 0) {
			/*
			 *	Only do this if *some* check pairs were returned
			 */
			if (paircompare(request, request->packet->vps, check_tmp, &request->reply->vps) == 0) {
				found = 1;
				RDEBUG2("User found in group %s",
					entry->name);
				/*
				 *	Now get the reply pairs since the paircompare matched
				 */
				if (!radius_xlat(querystr, sizeof(querystr), inst->config->authorize_group_reply_query, request, sql_escape_func, inst)) {
					radlog_request(L_ERR, 0, request, "Error generating query; rejecting user");
					/* Remove the grouup we added above */
					pairdelete(&request->packet->vps, PW_SQL_GROUP, 0, TAG_ANY);
					pairfree(&check_tmp);
					talloc_free(head);
					return -1;
				}
				if (sql_getvpdata(inst, &handle, request->reply, &reply_tmp, querystr) < 0) {
					radlog_request(L_ERR, 0, request, "Error retrieving reply pairs for group %s",
					       entry->name);
					/* Remove the grouup we added above */
					pairdelete(&request->packet->vps, PW_SQL_GROUP, 0, TAG_ANY);
					pairfree(&check_tmp);
					pairfree(&reply_tmp);
					talloc_free(head);
					return -1;
				}
				*dofallthrough = fallthrough(reply_tmp);
				radius_xlat_move(request, &request->reply->vps, &reply_tmp);
				radius_xlat_move(request, &request->config_items, &check_tmp);
			}
		} else {
			/*
			 *	rows == 0.  This is like having the username on a line
			 * 	in the user's file with no check vp's.  As such, we treat
			 *	it as found and add the reply attributes, so that we
			 *	match expected behavior
			 */
			found = 1;
			RDEBUG2("User found in group %s",
				entry->name);
			/*
			 *	Now get the reply pairs since the paircompare matched
			 */
			if (!radius_xlat(querystr, sizeof(querystr), inst->config->authorize_group_reply_query, request, sql_escape_func, inst)) {
				radlog_request(L_ERR, 0, request, "Error generating query; rejecting user");
				/* Remove the grouup we added above */
				pairdelete(&request->packet->vps, PW_SQL_GROUP, 0, TAG_ANY);
				pairfree(&check_tmp);
				talloc_free(head);
				return -1;
			}
			if (sql_getvpdata(inst, &handle, request->reply, &reply_tmp, querystr) < 0) {
				radlog_request(L_ERR, 0, request, "Error retrieving reply pairs for group %s",
				       entry->name);
				/* Remove the grouup we added above */
				pairdelete(&request->packet->vps, PW_SQL_GROUP, 0, TAG_ANY);
				pairfree(&check_tmp);
				pairfree(&reply_tmp);
				talloc_free(head);
				return -1;
			}
			*dofallthrough = fallthrough(reply_tmp);
			radius_xlat_move(request, &request->reply->vps, &reply_tmp);
			radius_xlat_move(request, &request->config_items, &check_tmp);
		}

		/*
		 * Delete the Sql-Group we added above
		 * And clear out the pairlists
		 */
		pairdelete(&request->packet->vps, PW_SQL_GROUP, 0, TAG_ANY);
		pairfree(&check_tmp);
		pairfree(&reply_tmp);
	}

	talloc_free(head);
	return found;
}


static int rlm_sql_detach(void *instance)
{
	rlm_sql_t *inst = instance;

	paircompare_unregister(PW_SQL_GROUP, sql_groupcmp);
	
	if (inst->config) {
		if (inst->pool) sql_poolfree(inst);

		if (inst->config->xlat_name) {
			xlat_unregister(inst->config->xlat_name, sql_xlat, instance);
		}
	}

	if (inst->handle) {
#if 0
		/*
		 *	FIXME: Call the modules 'destroy' function?
		 */
		dlclose(inst->handle);	/* ignore any errors */
#endif
	}

	return 0;
}

static int parse_sub_section(CONF_SECTION *parent,
	 		     rlm_sql_t *inst,
	 		     sql_acct_section_t **config,
	 		     rlm_components_t comp)
{
	CONF_SECTION *cs;

	const char *name = section_type_value[comp].section;
	
	cs = cf_section_sub_find(parent, name);
	if (!cs) {
		radlog(L_INFO, "rlm_sql (%s): Couldn't find configuration for "
		       "%s, will return NOOP for calls from this section",
		       inst->config->xlat_name, name);
		
		return 0;
	}
	
	*config = talloc_zero(parent, sql_acct_section_t);
	if (cf_section_parse(cs, *config, acct_section_config) < 0) {
		radlog(L_ERR, "rlm_sql (%s): Couldn't find configuration for "
		       "%s, will return NOOP for calls from this section",
		       inst->config->xlat_name, name);
		return -1;
	}
		
	(*config)->cs = cs;

	return 0;
}

static int rlm_sql_instantiate(CONF_SECTION *conf, void **instance)
{
	rlm_sql_t *inst;
	const char *xlat_name;

	*instance = inst = talloc_zero(conf, rlm_sql_t);
	if (!inst) return -1;
	
	/*
	 *	Cache the SQL-User-Name DICT_ATTR, so we can be slightly
	 *	more efficient about creating SQL-User-Name attributes.
	 */
	inst->sql_user = dict_attrbyname("SQL-User-Name");
	if (!inst->sql_user) {
		return -1;
	}
	
	/*
	 *	Export these methods, too.  This avoids RTDL_GLOBAL.
	 */
	inst->sql_set_user		= sql_set_user;
	inst->sql_get_socket		= sql_get_socket;
	inst->sql_release_socket	= sql_release_socket;
	inst->sql_escape_func		= sql_escape_func;
	inst->sql_query			= rlm_sql_query;
	inst->sql_select_query		= rlm_sql_select_query;
	inst->sql_fetch_row		= rlm_sql_fetch_row;
	
	inst->config = talloc_zero(inst, rlm_sql_config_t);
	inst->cs = conf;

	xlat_name = cf_section_name2(conf);
	if (xlat_name == NULL) {
		xlat_name = cf_section_name1(conf);
	} else {
		char *group_name;
		const DICT_ATTR *dattr;
		ATTR_FLAGS flags;

		/*
		 *	Allocate room for <instance>-SQL-Group
		 */
		group_name = talloc_asprintf(inst, "%s-SQL-Group", xlat_name);
		DEBUG("rlm_sql (%s): Creating new attribute %s",
		      xlat_name, group_name);

		memset(&flags, 0, sizeof(flags));
		if (dict_addattr(group_name, -1, 0, PW_TYPE_STRING, flags) < 0) {
			radlog(L_ERR, "rlm_sql (%s): Failed to create "
			       "attribute %s: %s", xlat_name, group_name,
			       fr_strerror());
			return -1;
		}

		dattr = dict_attrbyname(group_name);
		if (!dattr) {
			radlog(L_ERR, "rlm_sql (%s): Failed to create "
			       "attribute %s", xlat_name, group_name);
			return -1;
		}

		if (inst->config->groupmemb_query &&
		    inst->config->groupmemb_query[0]) {
			DEBUG("rlm_sql (%s): Registering sql_groupcmp for %s",
			      xlat_name, group_name);
			paircompare_register(dattr->attr, PW_USER_NAME,
					     sql_groupcmp, inst);
		}
	}
	
	rad_assert(xlat_name);

	/*
	 *	Register the SQL xlat function
	 */
	inst->config->xlat_name = talloc_strdup(inst->config, xlat_name);
	xlat_register(xlat_name, sql_xlat, inst);

	/*
	 *	If the configuration parameters can't be parsed, then fail.
	 */
	if ((cf_section_parse(conf, inst->config, module_config) < 0) ||
	    (parse_sub_section(conf, inst,
			       &inst->config->accounting,
			       RLM_COMPONENT_ACCT) < 0) ||
	    (parse_sub_section(conf, inst,
			       &inst->config->postauth,
			       RLM_COMPONENT_POST_AUTH) < 0)) {
		radlog(L_ERR, "rlm_sql (%s): Failed parsing configuration",
		       inst->config->xlat_name);
		return -1;
	}
		
	/*
	 *	Sanity check for crazy people.
	 */
	if (strncmp(inst->config->sql_driver_name, "rlm_sql_", 8) != 0) {
		radlog(L_ERR, "rlm_sql (%s): \"%s\" is NOT an SQL driver!",
		       inst->config->xlat_name, inst->config->sql_driver_name);
		return -1;
	}

	/*
	 *	Load the appropriate driver for our database
	 */
	inst->handle = lt_dlopenext(inst->config->sql_driver_name);
	if (inst->handle == NULL) {
		radlog(L_ERR, "Could not link driver %s: %s",
		       inst->config->sql_driver_name,
		       dlerror());
		radlog(L_ERR, "Make sure it (and all its dependent libraries!)"
		       "are in the search path of your system's ld.");
		return -1;
	}

	inst->module = (rlm_sql_module_t *) dlsym(inst->handle,
						  inst->config->sql_driver_name);
	if (!inst->module) {
		radlog(L_ERR, "Could not link symbol %s: %s",
		       inst->config->sql_driver_name,
		       dlerror());
		return -1;
	}
	
	if (inst->module->sql_instantiate) {
		CONF_SECTION *cs;
		const char *name;
		
		name = strrchr(inst->config->sql_driver_name, '_');
		if (!name) {
			name = inst->config->sql_driver_name;
		} else {
			name++;
		}
		
		cs = cf_section_sub_find(conf, name);
		if (!cs) {
			cs = cf_section_alloc(conf, name, NULL);
			if (!cs) {
				return -1;
			}
		}
		
		/*
		 *	It's up to the driver to register a destructor
		 */
		if (inst->module->sql_instantiate(cs, inst->config) < 0) {
			return -1;
		}
	}

	radlog(L_INFO, "rlm_sql (%s): Driver %s (module %s) loaded and linked",
	       inst->config->xlat_name, inst->config->sql_driver_name,
	       inst->module->name);

	/*
	 *	Initialise the connection pool for this instance
	 */
	radlog(L_INFO, "rlm_sql (%s): Attempting to connect to database \"%s\"",
	       inst->config->xlat_name, inst->config->sql_db);
	
	if (sql_socket_pool_init(inst) < 0) return -1;

	if (inst->config->groupmemb_query &&
	    inst->config->groupmemb_query[0]) {
		paircompare_register(PW_SQL_GROUP, PW_USER_NAME, sql_groupcmp, inst);
	}

	if (inst->config->do_clients) {
		if (generate_sql_clients(inst) == -1){
			radlog(L_ERR, "Failed to load clients from SQL.");
			return -1;
		}
	}

	return RLM_MODULE_OK;
}


static rlm_rcode_t rlm_sql_authorize(void *instance, REQUEST * request)
{
	int ret = RLM_MODULE_NOTFOUND;
	
	rlm_sql_t *inst = instance;
	rlm_sql_handle_t  *handle;
	
	VALUE_PAIR *check_tmp = NULL;
	VALUE_PAIR *reply_tmp = NULL;
	VALUE_PAIR *user_profile = NULL;

	int	dofallthrough = 1;
	int	rows;

	char	querystr[MAX_QUERY_LEN];

	/*
	 *  Set, escape, and check the user attr here
	 */
	if (sql_set_user(inst, request, NULL) < 0)
		return RLM_MODULE_FAIL;

	/*
	 *  Reserve a socket
	 *
	 *  After this point use goto error or goto release to cleanup sockets
	 *  temporary pairlists and temporary attributes.
	 */
	handle = sql_get_socket(inst);
	if (handle == NULL)
		goto error;

	/*
	 *  Query the check table to find any conditions associated with
	 *  this user/realm/whatever...
	 */
	if (inst->config->authorize_check_query &&
	    *inst->config->authorize_check_query) {
		if (!radius_xlat(querystr, sizeof(querystr), inst->config->authorize_check_query, request, sql_escape_func, inst)) {
			radlog_request(L_ERR, 0, request, "Error generating query; rejecting user");
	
			goto error;
		}
		
		rows = sql_getvpdata(inst, &handle, request, &check_tmp, querystr);
		if (rows < 0) {
			radlog_request(L_ERR, 0, request, "SQL query error; rejecting user");
	
			goto error;
		}
		
		/*
		 *  Only do this if *some* check pairs were returned
		 */
		if ((rows > 0) &&
		    (paircompare(request, request->packet->vps, check_tmp, &request->reply->vps) == 0)) {	
			RDEBUG2("User found in radcheck table");
			
			radius_xlat_move(request, &request->config_items, &check_tmp);
			
			ret = RLM_MODULE_OK;
		}
		
		/*
		 *  We only process reply table items if check conditions
		 *  were verified
		 */
		else
			goto skipreply;
	}
	
	if (inst->config->authorize_reply_query &&
	    *inst->config->authorize_reply_query) {
		/*
		 *  Now get the reply pairs since the paircompare matched
		 */
		if (!radius_xlat(querystr, sizeof(querystr), inst->config->authorize_reply_query, request, sql_escape_func, inst)) {
			radlog_request(L_ERR, 0, request, "Error generating query; rejecting user");
			
			goto error;
		}
		
		rows = sql_getvpdata(inst, &handle, request->reply, &reply_tmp, querystr);
		if (rows < 0) {
			radlog_request(L_ERR, 0, request, "SQL query error; rejecting user");

			goto error;
		}
		
		if (rows > 0) {
			if (!inst->config->read_groups) {
				dofallthrough = fallthrough(reply_tmp);
			}
			
			RDEBUG2("User found in radreply table");
			
			radius_xlat_move(request, &request->reply->vps, &reply_tmp);
			
			ret = RLM_MODULE_OK;
		}
	}
	
	skipreply:

	/*
	 *  Clear out the pairlists
	 */
	pairfree(&check_tmp);
	pairfree(&reply_tmp);

	/*
	 *  dofallthrough is set to 1 by default so that if the user information
	 *  is not found, we will still process groups.  If the user information,
	 *  however, *is* found, Fall-Through must be set in order to process
	 *  the groups as well.
	 */
	if (dofallthrough) {
		rows = rlm_sql_process_groups(inst, request, handle, &dofallthrough);
		if (rows < 0) {
			radlog_request(L_ERR, 0, request, "Error processing groups; rejecting user");

			goto error;
		}
		
		if (rows > 0)
			ret = RLM_MODULE_OK;
	}

	/*
	 *  Repeat the above process with the default profile or User-Profile
	 */
	if (dofallthrough) {
		/*
	 	 *  Check for a default_profile or for a User-Profile.
		 */
		user_profile = pairfind(request->config_items, PW_USER_PROFILE, 0, TAG_ANY);
		
		const char *profile = user_profile ?
				      user_profile->vp_strvalue :
				      inst->config->default_profile;
			
		if (!profile || !*profile)
			goto release;
			
		RDEBUG("Checking profile %s", profile);
		
		if (sql_set_user(inst, request, profile) < 0) {
			radlog_request(L_ERR, 0, request, "Error setting profile; rejecting user");

			goto error;
		}
		
		rows = rlm_sql_process_groups(inst, request, handle, &dofallthrough);
		if (rows < 0) {
			radlog_request(L_ERR, 0, request, "Error processing profile groups; rejecting user");

			goto error;
		}
		
		if (rows > 0)
			ret = RLM_MODULE_OK;
	}
	
	goto release;
	
	error:
	ret = RLM_MODULE_FAIL;
	
	release:
	sql_release_socket(inst, handle);
		
	pairfree(&check_tmp);
	pairfree(&reply_tmp);
	
	return ret;
}

/*
 *	Generic function for failing between a bunch of queries.
 *
 *	Uses the same principle as rlm_linelog, expanding the 'reference' config
 *	item using xlat to figure out what query it should execute.
 *
 *	If the reference matches multiple config items, and a query fails or
 *	doesn't update any rows, the next matching config item is used.
 *
 */
static int acct_redundant(rlm_sql_t *inst, REQUEST *request,
			  sql_acct_section_t *section)
{
	int	ret = RLM_MODULE_OK;

	rlm_sql_handle_t	*handle = NULL;
	int	sql_ret;
	int	numaffected = 0;

	CONF_ITEM  *item;
	CONF_PAIR  *pair;
	const char *attr = NULL;
	const char *value;

	char	path[MAX_STRING_LEN];
	char	querystr[MAX_QUERY_LEN];
	
	char	*p = path;

	rad_assert(section);
	
	if (section->reference[0] != '.')
		*p++ = '.';
	
	if (!radius_xlat(p, (sizeof(path) - (p - path)) - 1,
			section->reference, request, NULL, NULL))
		return RLM_MODULE_FAIL;

	item = cf_reference_item(NULL, section->cs, path);
	if (!item)
		return RLM_MODULE_FAIL;

	if (cf_item_is_section(item)){
		radlog(L_ERR, "Sections are not supported as references");
		
		return RLM_MODULE_FAIL;
	}
	
	pair = cf_itemtopair(item);
	attr = cf_pair_attr(pair);
	
	RDEBUG2("Using query template '%s'", attr);
	
	handle = sql_get_socket(inst);
	if (handle == NULL)
		return RLM_MODULE_FAIL;
		
	sql_set_user(inst, request, NULL);

	while (TRUE) {
		value = cf_pair_value(pair);
		if (!value) {
			RDEBUG("Ignoring null query");
			ret = RLM_MODULE_NOOP;
			
			goto release;
		}
		
		radius_xlat(querystr, sizeof(querystr), value, request,
			    sql_escape_func, inst);
		if (!*querystr) {
			RDEBUG("Ignoring null query");
			ret = RLM_MODULE_NOOP;
			
			goto release;
		}
		
		rlm_sql_query_log(inst, request, section, querystr);
		
		/*
		 *  If rlm_sql_query cannot use the socket it'll try and
		 *  reconnect. Reconnecting will automatically release
		 *  the current socket, and try to select a new one.
		 *
		 *  If we get SQL_DOWN it means all connections in the pool
		 *  were exhausted, and we couldn't create a new connection,
		 *  so we do not need to call sql_release_socket.
		 */
		sql_ret = rlm_sql_query(&handle, inst, querystr);	
		if (sql_ret == SQL_DOWN)
			return RLM_MODULE_FAIL;
		
		rad_assert(handle);
	
		/*
		 *  Assume all other errors are incidental, and just meant our
		 *  operation failed and its not a client or SQL syntax error.
		 */
		if (sql_ret == 0) {
			numaffected = (inst->module->sql_affected_rows)
					(handle, inst->config);
			if (numaffected > 0)
				break;
				
			RDEBUG("No records updated");
		}

		(inst->module->sql_finish_query)(handle, inst->config);
		
		/*
		 *  We assume all entries with the same name form a redundant
		 *  set of queries.
		 */
		pair = cf_pair_find_next(section->cs, pair, attr);
		
		if (!pair) {
			RDEBUG("No additional queries configured");
			
			ret = RLM_MODULE_NOOP;
			
			goto release;
		}

		RDEBUG("Trying next query...");
	}
	
	(inst->module->sql_finish_query)(handle, inst->config);

	release:
	sql_release_socket(inst, handle);

	return ret;
}

#ifdef WITH_ACCOUNTING

/*
 *	Accounting: Insert or update session data in our sql table
 */
static rlm_rcode_t rlm_sql_accounting(void *instance, REQUEST * request) {
	rlm_sql_t *inst = instance;		

	if (inst->config->accounting) {
		return acct_redundant(inst, request, inst->config->accounting);
	}
	
	return RLM_MODULE_NOOP;
}

#endif

#ifdef WITH_SESSION_MGMT
/*
 *	See if a user is already logged in. Sets request->simul_count to the
 *	current session count for this user.
 *
 *	Check twice. If on the first pass the user exceeds his
 *	max. number of logins, do a second pass and validate all
 *	logins by querying the terminal server (using eg. SNMP).
 */

static rlm_rcode_t rlm_sql_checksimul(void *instance, REQUEST * request) {
	rlm_sql_handle_t 	*handle;
	rlm_sql_t	*inst = instance;
	rlm_sql_row_t		row;
	char		querystr[MAX_QUERY_LEN];
	int		check = 0;
	uint32_t	ipno = 0;
	char	    *call_num = NULL;
	VALUE_PAIR      *vp;
	int		ret;
	uint32_t	nas_addr = 0;
	int		nas_port = 0;

	/* If simul_count_query is not defined, we don't do any checking */
	if (!inst->config->simul_count_query ||
	    (inst->config->simul_count_query[0] == 0)) {
		return RLM_MODULE_NOOP;
	}

	if((request->username == NULL) || (request->username->length == 0)) {
		radlog_request(L_ERR, 0, request,
					   "Zero Length username not permitted\n");
		return RLM_MODULE_INVALID;
	}


	if(sql_set_user(inst, request, NULL) < 0)
		return RLM_MODULE_FAIL;

	radius_xlat(querystr, sizeof(querystr), inst->config->simul_count_query, request, sql_escape_func, inst);

	/* initialize the sql socket */
	handle = sql_get_socket(inst);
	if(handle == NULL)
		return RLM_MODULE_FAIL;

	if(rlm_sql_select_query(&handle, inst, querystr)) {
		sql_release_socket(inst, handle);
		return RLM_MODULE_FAIL;
	}

	ret = rlm_sql_fetch_row(&handle, inst);
	if (ret != 0) {
		(inst->module->sql_finish_select_query)(handle, inst->config);
		sql_release_socket(inst, handle);
		return RLM_MODULE_FAIL;
	}

	row = handle->row;
	if (row == NULL) {
		(inst->module->sql_finish_select_query)(handle, inst->config);
		sql_release_socket(inst, handle);
		return RLM_MODULE_FAIL;
	}

	request->simul_count = atoi(row[0]);
	(inst->module->sql_finish_select_query)(handle, inst->config);

	if(request->simul_count < request->simul_max) {
		sql_release_socket(inst, handle);
		return RLM_MODULE_OK;
	}

	/*
	 *	Looks like too many sessions, so let's start verifying
	 *	them, unless told to rely on count query only.
	 */
	if (!inst->config->simul_verify_query ||
	    (inst->config->simul_verify_query[0] == '\0')) {
		sql_release_socket(inst, handle);
		return RLM_MODULE_OK;
	}

	radius_xlat(querystr, sizeof(querystr), inst->config->simul_verify_query, request, sql_escape_func, inst);
	if(rlm_sql_select_query(&handle, inst, querystr)) {
		sql_release_socket(inst, handle);
		return RLM_MODULE_FAIL;
	}

	/*
	 *      Setup some stuff, like for MPP detection.
	 */
	request->simul_count = 0;

	if ((vp = pairfind(request->packet->vps, PW_FRAMED_IP_ADDRESS, 0, TAG_ANY)) != NULL)
		ipno = vp->vp_ipaddr;
	if ((vp = pairfind(request->packet->vps, PW_CALLING_STATION_ID, 0, TAG_ANY)) != NULL)
		call_num = vp->vp_strvalue;


	while (rlm_sql_fetch_row(&handle, inst) == 0) {
		row = handle->row;
		if (row == NULL)
			break;
		if (!row[2]){
			(inst->module->sql_finish_select_query)(handle, inst->config);
			sql_release_socket(inst, handle);
			RDEBUG("Cannot zap stale entry. No username present in entry.", inst->config->xlat_name);
			return RLM_MODULE_FAIL;
		}
		if (!row[1]){
			(inst->module->sql_finish_select_query)(handle, inst->config);
			sql_release_socket(inst, handle);
			RDEBUG("Cannot zap stale entry. No session id in entry.", inst->config->xlat_name);
			return RLM_MODULE_FAIL;
		}
		if (row[3])
			nas_addr = inet_addr(row[3]);
		if (row[4])
			nas_port = atoi(row[4]);

		check = rad_check_ts(nas_addr, nas_port, row[2], row[1]);

		if (check == 0) {
			/*
			 *	Stale record - zap it.
			 */
			if (inst->config->deletestalesessions == TRUE) {
				uint32_t framed_addr = 0;
				char proto = 0;
				int sess_time = 0;

				if (row[5])
					framed_addr = inet_addr(row[5]);
				if (row[7]){
					if (strcmp(row[7], "PPP") == 0)
						proto = 'P';
					else if (strcmp(row[7], "SLIP") == 0)
						proto = 'S';
				}
				if (row[8])
					sess_time = atoi(row[8]);
				session_zap(request, nas_addr, nas_port,
					    row[2], row[1], framed_addr,
					    proto, sess_time);
			}
		}
		else if (check == 1) {
			/*
			 *	User is still logged in.
			 */
			++request->simul_count;

			/*
			 *      Does it look like a MPP attempt?
			 */
			if (row[5] && ipno && inet_addr(row[5]) == ipno)
				request->simul_mpp = 2;
			else if (row[6] && call_num &&
				!strncmp(row[6],call_num,16))
				request->simul_mpp = 2;
		}
		else {
			/*
			 *      Failed to check the terminal server for
			 *      duplicate logins: return an error.
			 */
			(inst->module->sql_finish_select_query)(handle, inst->config);
			sql_release_socket(inst, handle);
			radlog_request(L_ERR, 0, request, "Failed to check the terminal server for user '%s'.", row[2]);
			return RLM_MODULE_FAIL;
		}
	}

	(inst->module->sql_finish_select_query)(handle, inst->config);
	sql_release_socket(inst, handle);

	/*
	 *	The Auth module apparently looks at request->simul_count,
	 *	not the return value of this module when deciding to deny
	 *	a call for too many sessions.
	 */
	return RLM_MODULE_OK;
}
#endif

/*
 *	Postauth: Write a record of the authentication attempt
 */
static rlm_rcode_t rlm_sql_postauth(void *instance, REQUEST * request) {
	rlm_sql_t *inst = instance;
	
	if (inst->config->postauth) {
		return acct_redundant(inst, request, inst->config->postauth);
	}
	
	return RLM_MODULE_NOOP;
}

/*
 *	Execute postauth_query after authentication
 */


/* globally exported name */
module_t rlm_sql = {
	RLM_MODULE_INIT,
	"SQL",
	RLM_TYPE_THREAD_SAFE,	/* type: reserved */
	rlm_sql_instantiate,	/* instantiation */
	rlm_sql_detach,		/* detach */
	{
		NULL,			/* authentication */
		rlm_sql_authorize,	/* authorization */
		NULL,			/* preaccounting */
#ifdef WITH_ACCOUNTING
		rlm_sql_accounting,	/* accounting */
#else
		NULL,
#endif
#ifdef WITH_SESSION_MGMT
		rlm_sql_checksimul,	/* checksimul */
#else
		NULL,
#endif
		NULL,			/* pre-proxy */
		NULL,			/* post-proxy */
		rlm_sql_postauth	/* post-auth */
	},
};
