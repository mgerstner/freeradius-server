/*
 *   This library is free software; you can redistribute it and/or
 *   modify it under the terms of the GNU Lesser General Public
 *   License as published by the Free Software Foundation; either
 *   version 2.1 of the License, or (at your option) any later version.
 *
 *   This library is distributed in the hope that it will be useful,
 *   but WITHOUT ANY WARRANTY; without even the implied warranty of
 *   MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the GNU
 *   Lesser General Public License for more details.
 *
 *   You should have received a copy of the GNU Lesser General Public
 *   License along with this library; if not, write to the Free Software
 *   Foundation, Inc., 51 Franklin St, Fifth Floor, Boston, MA 02110-1301, USA
 */

/**
 * $Id$
 *
 * @file radius.c
 * @brief Functions to decode RADIUS attributes
 *
 * @copyright 2000-2003,2006-2015  The FreeRADIUS server project
 */
#include <freeradius-devel/libradius.h>
#include <freeradius-devel/md5.h>

static uint8_t nullvector[AUTH_VECTOR_LEN] = { 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0 }; /* for CoA decode */
#if 1
#define VP_TRACE(_x, ...) printf("%s[%i]: " _x "\n", __FUNCTION__, __LINE__, ## __VA_ARGS__)

static void VP_HEX_DUMP(char const *msg, uint8_t const *data, size_t len)
{
	size_t i;

	printf("--- %s ---\n", msg);
	for (i = 0; i < len; i++) {
		if ((i & 0x0f) == 0) printf("%04x: ", (unsigned int) i);
		printf("%02x ", data[i]);
		if ((i & 0x0f) == 0x0f) printf("\n");
	}
	if ((len == 0x0f) || ((len & 0x0f) != 0x0f)) printf("\n");
	fflush(stdout);
}

#else
#define VP_TRACE(_x, ...)
#define VP_HEX_DUMP(_x, _y, _z)
#endif

/** Decode Tunnel-Password encrypted attributes
 *
 * Defined in RFC-2868, this uses a two char SALT along with the
 * initial intermediate value, to differentiate it from the
 * above.
 */
int fr_radius_decode_tunnel_password(uint8_t *passwd, size_t *pwlen, char const *secret, uint8_t const *vector)
{
	FR_MD5_CTX	context, old;
	uint8_t		digest[AUTH_VECTOR_LEN];
	int		secretlen;
	size_t		i, n, encrypted_len, reallen;

	encrypted_len = *pwlen;

	/*
	 *	We need at least a salt.
	 */
	if (encrypted_len < 2) {
		fr_strerror_printf("tunnel password is too short");
		return -1;
	}

	/*
	 *	There's a salt, but no password.  Or, there's a salt
	 *	and a 'data_len' octet.  It's wrong, but at least we
	 *	can figure out what it means: the password is empty.
	 *
	 *	Note that this means we ignore the 'data_len' field,
	 *	if the attribute length tells us that there's no
	 *	more data.  So the 'data_len' field may be wrong,
	 *	but that's ok...
	 */
	if (encrypted_len <= 3) {
		passwd[0] = 0;
		*pwlen = 0;
		return 0;
	}

	encrypted_len -= 2;		/* discount the salt */

	/*
	 *	Use the secret to setup the decryption digest
	 */
	secretlen = strlen(secret);

	fr_md5_init(&context);
	fr_md5_update(&context, (uint8_t const *) secret, secretlen);
	fr_md5_copy(&old, &context); /* save intermediate work */
	/*
	 *	Set up the initial key:
	 *
	 *	 b(1) = MD5(secret + vector + salt)
	 */
	fr_md5_update(&context, vector, AUTH_VECTOR_LEN);
	fr_md5_update(&context, passwd, 2);

	reallen = 0;
	for (n = 0; n < encrypted_len; n += AUTH_PASS_LEN) {
		size_t base;
		size_t block_len = AUTH_PASS_LEN;

		/*
		 *	Ensure we don't overflow the input on MD5
		 */
		if ((n + 2 + AUTH_PASS_LEN) > *pwlen) {
			block_len = *pwlen - n - 2;
		}

		if (n == 0) {
			base = 1;

			fr_md5_final(digest, &context);

			fr_md5_copy(&context, &old);

			/*
			 *	A quick check: decrypt the first octet
			 *	of the password, which is the
			 *	'data_len' field.  Ensure it's sane.
			 */
			reallen = passwd[2] ^ digest[0];
			if (reallen > encrypted_len) {
				fr_strerror_printf("tunnel password is too long for the attribute");
				return -1;
			}

			fr_md5_update(&context, passwd + 2, block_len);

		} else {
			base = 0;

			fr_md5_final(digest, &context);

			fr_md5_copy(&context, &old);
			fr_md5_update(&context, passwd + n + 2, block_len);
		}

		for (i = base; i < block_len; i++) {
			passwd[n + i - 1] = passwd[n + i + 2] ^ digest[i];
		}
	}

	*pwlen = reallen;
	passwd[reallen] = 0;

	return reallen;
}

/** Decode password
 *
 */
int fr_radius_decode_password(char *passwd, size_t pwlen, char const *secret, uint8_t const *vector)
{
	FR_MD5_CTX	context, old;
	uint8_t		digest[AUTH_VECTOR_LEN];
	int		i;
	size_t		n, secretlen;

	/*
	 *	The RFC's say that the maximum is 128.
	 *	The buffer we're putting it into above is 254, so
	 *	we don't need to do any length checking.
	 */
	if (pwlen > 128) pwlen = 128;

	/*
	 *	Catch idiots.
	 */
	if (pwlen == 0) goto done;

	/*
	 *	Use the secret to setup the decryption digest
	 */
	secretlen = strlen(secret);

	fr_md5_init(&context);
	fr_md5_update(&context, (uint8_t const *) secret, secretlen);
	fr_md5_copy(&old, &context);	/* save intermediate work */

	/*
	 *	The inverse of the code above.
	 */
	for (n = 0; n < pwlen; n += AUTH_PASS_LEN) {
		if (n == 0) {
			fr_md5_update(&context, vector, AUTH_VECTOR_LEN);
			fr_md5_final(digest, &context);

			fr_md5_copy(&context, &old);
			if (pwlen > AUTH_PASS_LEN) {
				fr_md5_update(&context, (uint8_t *) passwd, AUTH_PASS_LEN);
			}
		} else {
			fr_md5_final(digest, &context);

			fr_md5_copy(&context, &old);
			if (pwlen > (n + AUTH_PASS_LEN)) {
				fr_md5_update(&context, (uint8_t *) passwd + n, AUTH_PASS_LEN);
			}
		}

		for (i = 0; i < AUTH_PASS_LEN; i++) passwd[i + n] ^= digest[i];
	}

 done:
	passwd[pwlen] = '\0';
	return strlen(passwd);
}

/** Check if a set of RADIUS formatted TLVs are OK
 *
 */
int fr_radius_decode_tlv_ok(uint8_t const *data, size_t length, size_t dv_type, size_t dv_length)
{
	uint8_t const *end = data + length;

	VP_TRACE("Checking TLV %u/%u", (unsigned int) dv_type, (unsigned int) dv_length);

	VP_HEX_DUMP("tlv_ok", data, length);

	if ((dv_length > 2) || (dv_type == 0) || (dv_type > 4)) {
		fr_strerror_printf("%s: Invalid arguments", __FUNCTION__);
		return -1;
	}

	while (data < end) {
		size_t attrlen;

		if ((data + dv_type + dv_length) > end) {
			fr_strerror_printf("Attribute header overflow");
			return -1;
		}

		switch (dv_type) {
		case 4:
			if ((data[0] == 0) && (data[1] == 0) &&
			    (data[2] == 0) && (data[3] == 0)) {
			zero:
				fr_strerror_printf("Invalid attribute 0");
				return -1;
			}

			if (data[0] != 0) {
				fr_strerror_printf("Invalid attribute > 2^24");
				return -1;
			}
			break;

		case 2:
			if ((data[0] == 0) && (data[1] == 0)) goto zero;
			break;

		case 1:
			/*
			 *	Zero is allowed, because the Colubris
			 *	people are dumb and use it.
			 */
			break;

		default:
			fr_strerror_printf("Internal sanity check failed");
			return -1;
		}

		switch (dv_length) {
		case 0:
			return 0;

		case 2:
			if (data[dv_type] != 0) {
				fr_strerror_printf("Attribute is longer than 256 octets");
				return -1;
			}
			/* FALL-THROUGH */
		case 1:
			attrlen = data[dv_type + dv_length - 1];
			break;


		default:
			fr_strerror_printf("Internal sanity check failed");
			return -1;
		}

		if (attrlen < (dv_type + dv_length)) {
			fr_strerror_printf("Attribute header has invalid length");
			return -1;
		}

		if (attrlen > length) {
			fr_strerror_printf("Attribute overflows container");
			return -1;
		}

		data += attrlen;
		length -= attrlen;
	}

	return 0;
}

/** Convert a "concatenated" attribute to one long VP
 *
 */
static ssize_t decode_concat(TALLOC_CTX *ctx,
			     fr_dict_attr_t const *parent, uint8_t const *start,
			     size_t const packetlen, VALUE_PAIR **pvp)
{
	size_t		total;
	uint8_t		attr;
	uint8_t const	*ptr = start;
	uint8_t const	*end = start + packetlen;
	uint8_t		*p;
	VALUE_PAIR	*vp;

	total = 0;
	attr = ptr[0];

	/*
	 *	The packet has already been sanity checked, so we
	 *	don't care about walking off of the end of it.
	 */
	while (ptr < end) {
		total += ptr[1] - 2;

		ptr += ptr[1];

		/*
		 *	Attributes MUST be consecutive.
		 */
		if (ptr[0] != attr) break;
	}

	vp = fr_pair_afrom_da(ctx, parent);
	if (!vp) return -1;

	vp->vp_length = total;
	vp->vp_octets = p = talloc_array(vp, uint8_t, vp->vp_length);
	if (!p) {
		fr_pair_list_free(&vp);
		return -1;
	}

	total = 0;
	ptr = start;
	while (total < vp->vp_length) {
		memcpy(p, ptr + 2, ptr[1] - 2);
		p += ptr[1] - 2;
		total += ptr[1] - 2;
		ptr += ptr[1];
	}

	*pvp = vp;
	return ptr - start;
}


/** Convert TLVs to one or more VPs
 *
 */
ssize_t fr_radius_decode_tlv(TALLOC_CTX *ctx,
			     RADIUS_PACKET *packet, RADIUS_PACKET const *original,
			     char const *secret, fr_dict_attr_t const *parent,
			     uint8_t const *start, size_t length,
			     VALUE_PAIR **pvp)
{
	uint8_t const		*data = start;
	fr_dict_attr_t const	*child;
	VALUE_PAIR		*head, **tail;

	if (length < 3) return -1; /* type, length, value */

	VP_HEX_DUMP("tlvs", data, length);

	if (fr_radius_decode_tlv_ok(data, length, 1, 1) < 0) return -1;

	head = NULL;
	tail = &head;

	while (data < (start + length)) {
		ssize_t tlv_len;

		child = fr_dict_attr_child_by_num(parent, data[0]);
		if (!child) {
			fr_dict_attr_t *unknown_child;

			VP_TRACE("Failed to find child %u of TLV %s", data[0], parent->name);

			/*
			 *	Build an unknown attr
			 */
			unknown_child = fr_dict_unknown_afrom_fields(ctx, parent, parent->vendor, data[0]);
			if (!unknown_child) {
				fr_pair_list_free(&head);
				return -1;
			}
			unknown_child->parent = parent;	/* Needed for re-encoding */
			child = unknown_child;
		}
		VP_TRACE("Attr context changed %s -> %s", parent->name, child->name);

		tlv_len = fr_radius_decode_pair_value(ctx, packet, original, secret, child,
						      data + 2, data[1] - 2, data[1] - 2, tail);
		if (tlv_len < 0) {
			fr_pair_list_free(&head);
			return -1;
		}
		if (*tail) tail = &((*tail)->next);
		data += data[1];
	}

	*pvp = head;
	return length;
}

/** Convert a top-level VSA to a VP.
 *
 * "length" can be LONGER than just this sub-vsa.
 */
static ssize_t decode_vsa_internal(TALLOC_CTX *ctx, RADIUS_PACKET *packet,
				   RADIUS_PACKET const *original,
				   char const *secret, fr_dict_vendor_t *dv,
				   fr_dict_attr_t const *parent, uint8_t const *data, size_t length,
				   VALUE_PAIR **pvp)
{
	unsigned int		attribute;
	ssize_t			attrlen, my_len;
	fr_dict_attr_t const	*da;

	/*
	 *	Parent must be a vendor
	 */
	if (!fr_assert(parent->type == PW_TYPE_VENDOR)) {
		fr_strerror_printf("%s: Internal sanity check failed", __FUNCTION__);
		return -1;
	}

	VP_TRACE("Length %u", (unsigned int) length);

#ifndef NDEBUG
	if (length <= (dv->type + dv->length)) {
		fr_strerror_printf("%s: Failure to call fr_radius_decode_tlv_ok", __FUNCTION__);
		return -1;
	}
#endif

	switch (dv->type) {
	case 4:
		/* data[0] must be zero */
		attribute = data[1] << 16;
		attribute |= data[2] << 8;
		attribute |= data[3];
		break;

	case 2:
		attribute = data[0] << 8;
		attribute |= data[1];
		break;

	case 1:
		attribute = data[0];
		break;

	default:
		fr_strerror_printf("%s: Internal sanity check failed", __FUNCTION__);
		return -1;
	}

	switch (dv->length) {
	case 2:
		/* data[dv->type] must be zero, from fr_radius_decode_tlv_ok() */
		attrlen = data[dv->type + 1];
		break;

	case 1:
		attrlen = data[dv->type];
		break;

	case 0:
		attrlen = length;
		break;

	default:
		fr_strerror_printf("%s: Internal sanity check failed", __FUNCTION__);
		return -1;
	}

	/*
	 *	See if the VSA is known.
	 */
	da = fr_dict_attr_child_by_num(parent, attribute);
	if (!da) da = fr_dict_unknown_afrom_fields(ctx, parent, dv->vendorpec, attribute);
	if (!da) return -1;
	VP_TRACE("Attr context changed %s -> %s", da->parent->name, da->name);

	my_len = fr_radius_decode_pair_value(ctx, packet, original, secret, da,
					     data + dv->type + dv->length,
					     attrlen - (dv->type + dv->length),
					     attrlen - (dv->type + dv->length),
					     pvp);
	if (my_len < 0) return my_len;

	return attrlen;
}


/** Convert a fragmented extended attr to a VP
 *
 * Format is:
 *
 * attr
 * length
 * extended-attr
 * flag
 * data...
 *
 * But for the first fragment, we get passed a pointer to the "extended-attr"
 */
static ssize_t decode_extended(TALLOC_CTX *ctx, RADIUS_PACKET *packet,
			       RADIUS_PACKET const *original,
			       char const *secret, fr_dict_attr_t const *parent,
			       uint8_t const *data,
			       size_t attrlen, size_t packetlen,
			       VALUE_PAIR **pvp)
{
	ssize_t		rcode;
	size_t		fraglen;
	uint8_t		*head, *tail;
	uint8_t const	*frag, *end;
	uint8_t const	*attr;
	int		fragments;
	bool		last_frag;

	if (attrlen < 3) return -1;

	/*
	 *	Calculate the length of all of the fragments.  For
	 *	now, they MUST be contiguous in the packet, and they
	 *	MUST be all of the same TYPE and EXTENDED-TYPE
	 */
	attr = data - 2;
	fraglen = attrlen - 2;
	frag = data + attrlen;
	end = data + packetlen;
	fragments = 1;
	last_frag = false;

	while (frag < end) {
		if (last_frag ||
		    (frag[0] != attr[0]) ||
		    (frag[1] < 4) ||		       /* too short for long-extended */
		    (frag[2] != attr[2]) ||
		    ((frag + frag[1]) > end)) {		/* overflow */
			end = frag;
			break;
		}

		last_frag = ((frag[3] & 0x80) == 0);

		fraglen += frag[1] - 4;
		frag += frag[1];
		fragments++;
	}

	head = tail = malloc(fraglen);
	if (!head) return -1;

	VP_TRACE("Fragments %d, total length %d", fragments, (int) fraglen);

	/*
	 *	And again, but faster and looser.
	 *
	 *	We copy the first fragment, followed by the rest of
	 *	the fragments.
	 */
	frag = attr;

	while (fragments >  0) {
		memcpy(tail, frag + 4, frag[1] - 4);
		tail += frag[1] - 4;
		frag += frag[1];
		fragments--;
	}

	VP_HEX_DUMP("long-extended fragments", head, fraglen);

	rcode = fr_radius_decode_pair_value(ctx, packet, original, secret, parent,
					    head, fraglen, fraglen, pvp);
	free(head);
	if (rcode < 0) return rcode;

	return end - data;
}

/** Convert a Vendor-Specific WIMAX to vps
 *
 * @note Called ONLY for Vendor-Specific
 */
static ssize_t decode_wimax(TALLOC_CTX *ctx,
			    RADIUS_PACKET *packet, RADIUS_PACKET const *original,
			    char const *secret, uint32_t vendor,
			    fr_dict_attr_t const *parent, uint8_t const *data,
			    size_t attrlen, size_t packetlen,
			    VALUE_PAIR **pvp)
{
	ssize_t			rcode;
	size_t			fraglen;
	bool			last_frag;
	uint8_t			*head, *tail;
	uint8_t	const		*frag, *end;
	fr_dict_attr_t const	*da;

	if (attrlen < 8) return -1;

	if (((size_t) (data[5] + 4)) != attrlen) return -1;

	da = fr_dict_attr_child_by_num(parent, data[4]);
	if (!da) da = fr_dict_unknown_afrom_fields(ctx, parent, vendor, data[4]);
	if (!da) return -1;
	VP_TRACE("Attr context changed %s -> %s", da->parent->name, da->name);

	if ((data[6] & 0x80) == 0) {
		rcode = fr_radius_decode_pair_value(ctx, packet, original, secret, da,
						    data + 7, data[5] - 3, data[5] - 3,
						    pvp);
		if (rcode < 0) return -1;
		return 7 + rcode;
	}

	/*
	 *	Calculate the length of all of the fragments.  For
	 *	now, they MUST be contiguous in the packet, and they
	 *	MUST be all of the same VSA, WiMAX, and WiMAX-attr.
	 *
	 *	The first fragment doesn't have a RADIUS attribute
	 *	header, so it needs to be treated a little special.
	 */
	fraglen = data[5] - 3;
	frag = data + attrlen;
	end = data + packetlen;
	last_frag = false;

	while (frag < end) {
		if (last_frag ||
		    (frag[0] != PW_VENDOR_SPECIFIC) ||
		    (frag[1] < 9) ||		       /* too short for wimax */
		    ((frag + frag[1]) > end) ||		/* overflow */
		    (memcmp(frag + 2, data, 4) != 0) || /* not wimax */
		    (frag[6] != data[4]) || /* not the same wimax attr */
		    ((frag[7] + 6) != frag[1])) { /* doesn't fill the attr */
			end = frag;
			break;
		}

		last_frag = ((frag[8] & 0x80) == 0);

		fraglen += frag[7] - 3;
		frag += frag[1];
	}

	head = tail = malloc(fraglen);
	if (!head) return -1;

	/*
	 *	And again, but faster and looser.
	 *
	 *	We copy the first fragment, followed by the rest of
	 *	the fragments.
	 */
	frag = data;

	memcpy(tail, frag + 4 + 3, frag[4 + 1] - 3);
	tail += frag[4 + 1] - 3;
	frag += attrlen;	/* should be frag[1] - 7 */

	/*
	 *	frag now points to RADIUS attributes
	 */
	do {
		memcpy(tail, frag + 2 + 4 + 3, frag[2 + 4 + 1] - 3);
		tail += frag[2 + 4 + 1] - 3;
		frag += frag[1];
	} while (frag < end);

	VP_HEX_DUMP("Wimax fragments", head, fraglen);

	rcode = fr_radius_decode_pair_value(ctx, packet, original, secret, da, head, fraglen, fraglen, pvp);
	free(head);
	if (rcode < 0) return rcode;

	return end - data;
}


/** Convert a top-level VSA to one or more VPs
 *
 */
static ssize_t decode_vsa(TALLOC_CTX *ctx, RADIUS_PACKET *packet,
			  RADIUS_PACKET const *original,
			  char const *secret,
			  fr_dict_attr_t const *parent, uint8_t const *data,
			  size_t attrlen, size_t packetlen,
			  VALUE_PAIR **pvp)
{
	size_t			total;
	ssize_t			rcode;
	uint32_t		vendor;
	fr_dict_vendor_t	*dv;
	VALUE_PAIR		*head, **tail;
	fr_dict_vendor_t	my_dv;
	fr_dict_attr_t const	*vendor_da;

	/*
	 *	Container must be a VSA
	 */
	if (!fr_assert(parent->type == PW_TYPE_VSA)) return -1;

	if (attrlen > packetlen) return -1;
	if (attrlen < 5) return -1; /* vid, value */
	if (data[0] != 0) return -1; /* we require 24-bit VIDs */

	VP_TRACE("Decoding VSA");

	memcpy(&vendor, data, 4);
	vendor = ntohl(vendor);

	/*
	 *	Verify that the parent (which should be a VSA)
	 *	contains a fake attribute representing the vendor.
	 *
	 *	If it doesn't then this vendor is unknown, but
	 *	(unlike DHCP) we know vendor attributes have a
	 *	standard format, so we can decode the data anyway.
	 */
	vendor_da = fr_dict_attr_child_by_num(parent, vendor);
	if (!vendor_da) {
		/*
		 *	RFC format is 1 octet type, 1 octet length
		 */
		if (fr_radius_decode_tlv_ok(data + 4, attrlen - 4, 1, 1) < 0) {
			VP_TRACE("Unknown TLVs not OK: %s", fr_strerror());
			return -1;
		}

		if (fr_dict_unknown_vendor_afrom_num(ctx, &vendor_da, parent, vendor) < 0) return -1;

		/*
		 *	Create an unknown DV too...
		 */
		memset(&my_dv, 0, sizeof(my_dv));
		dv = &my_dv;
		dv->vendorpec = vendor;
		dv->type = 1;
		dv->length = 1;

		goto create_attrs;
	} else {
		/*
		 *	We found an attribute representing the vendor
		 *	so it *MUST* exist in the vendor tree.
		 */
		dv = fr_dict_vendor_by_num(vendor);
		if (!fr_assert(dv)) return -1;
	}
	VP_TRACE("Attr context %s -> %s", parent->name, vendor_da->name);

	/*
	 *	WiMAX craziness
	 */
	if ((vendor == VENDORPEC_WIMAX) && dv->flags) {
		rcode = decode_wimax(ctx, packet, original, secret, vendor,
				     vendor_da, data, attrlen, packetlen, pvp);
		return rcode;
	}

	/*
	 *	VSAs should normally be in TLV format.
	 */
	if (fr_radius_decode_tlv_ok(data + 4, attrlen - 4, dv->type, dv->length) < 0) {
		VP_TRACE("TLVs not OK: %s", __FUNCTION__, fr_strerror());
		return -1;
	}

	/*
	 *	There may be more than one VSA in the
	 *	Vendor-Specific.  If so, loop over them all.
	 */
create_attrs:
	data += 4;
	attrlen -= 4;
	packetlen -= 4;
	total = 4;
	head = NULL;
	tail = &head;

	while (attrlen > 0) {
		ssize_t vsa_len;

		/*
		 *	Vendor attributes can have subattributes (if you hadn't guessed)
		 */
		vsa_len = decode_vsa_internal(ctx, packet, original, secret, dv, vendor_da, data, attrlen, tail);
		if (vsa_len < 0) {
			fr_strerror_printf("%s: Internal sanity check %d", __FUNCTION__, __LINE__);
			fr_pair_list_free(&head);
			fr_dict_attr_free(&vendor_da);
			return -1;
		}

		/*
		 *	Vendors can send zero-length VSAs.
		 */
		if (*tail) tail = &((*tail)->next);

		data += vsa_len;
		attrlen -= vsa_len;
		packetlen -= vsa_len;
		total += vsa_len;
	}

	*pvp = head;

	/*
	 *	When the unknown attributes were created by
	 *	decode_vsa_internal, the hierachy between that unknown
	 *	attribute and first known attribute was cloned
	 *	meaning we can now free the unknown vendor.
	 */
	fr_dict_attr_free(&vendor_da);	/* Only frees unknown vendors */

	return total;
}

/** Create any kind of VP from the attribute contents
 *
 * "length" is AT LEAST the length of this attribute, as we
 * expect the caller to have verified the data with
 * rad_packet_ok().  "length" may be up to the length of the
 * packet.
 *
 * @return
 *	- Length on success.
 *	- -1 on failure.
 */
ssize_t fr_radius_decode_pair_value(TALLOC_CTX *ctx,
				    RADIUS_PACKET *packet, RADIUS_PACKET const *original,
				    char const *secret,
				    fr_dict_attr_t const *parent, uint8_t const *start,
				    size_t const attrlen, size_t const packetlen,
				    VALUE_PAIR **pvp)
{
	int8_t			tag = TAG_NONE;
	size_t			datalen;
	ssize_t			rcode;
	uint32_t		vendor;
	fr_dict_attr_t const	*child;
	VALUE_PAIR		*vp;
	uint8_t const		*data = start;
	char			*p;
	uint8_t			buffer[256];

	/*
	 *	FIXME: Attrlen can be larger than 253 for extended attrs!
	 */
	if (!parent || (attrlen > packetlen) ||
	    ((attrlen > 253) && (attrlen != packetlen)) ||
	    (attrlen > 128*1024)) {
		fr_strerror_printf("%s: Invalid arguments", __FUNCTION__);
		return -1;
	}

	VP_HEX_DUMP(__FUNCTION__ , start, attrlen);

	VP_TRACE("Parent %s len %zu ... %zu", parent->name, attrlen, packetlen);

	datalen = attrlen;

	/*
	 *	Hacks for CUI.  The WiMAX spec says that it can be
	 *	zero length, even though this is forbidden by the
	 *	RADIUS specs.  So... we make a special case for it.
	 */
	if (attrlen == 0) {
		if (!((parent->vendor == 0) && (parent->attr == PW_CHARGEABLE_USER_IDENTITY))) {
			*pvp = NULL;
			return 0;
		}

#ifndef NDEBUG
		/*
		 *	Hacks for Coverity.  Editing the dictionary
		 *	will break assumptions about CUI.  We know
		 *	this, but Coverity doesn't.
		 */
		if (parent->type != PW_TYPE_OCTETS) return -1;
#endif

		data = NULL;
		datalen = 0;
		goto alloc_cui;	/* skip everything */
	}

	/*
	 *	Hacks for tags.  If the attribute is capable of
	 *	encoding a tag, and there's room for the tag, and
	 *	there is a tag, or it's encrypted with Tunnel-Password,
	 *	then decode the tag.
	 */
	if (parent->flags.has_tag && (datalen > 1) && ((data[0] < 0x20) ||
						       (parent->flags.encrypt == FLAG_ENCRYPT_TUNNEL_PASSWORD))) {
		/*
		 *	Only "short" attributes can be encrypted.
		 */
		if (datalen >= sizeof(buffer)) return -1;

		if (parent->type == PW_TYPE_STRING) {
			memcpy(buffer, data + 1, datalen - 1);
			tag = data[0];
			datalen -= 1;

		} else if (parent->type == PW_TYPE_INTEGER) {
			memcpy(buffer, data, attrlen);
			tag = buffer[0];
			buffer[0] = 0;

		} else {
			return -1; /* only string and integer can have tags */
		}

		data = buffer;
	}

	/*
	 *	Decrypt the attribute.
	 */
	if (secret && packet && (parent->flags.encrypt != FLAG_ENCRYPT_NONE)) {
		VP_TRACE("Decrypting type %u", parent->flags.encrypt);
		/*
		 *	Encrypted attributes can only exist for the
		 *	old-style format.  Extended attributes CANNOT
		 *	be encrypted.
		 */
		if (attrlen > 253) return -1;

		if (data == start) memcpy(buffer, data, attrlen);
		data = buffer;

		switch (parent->flags.encrypt) { /* can't be tagged */
		/*
		 *  User-Password
		 */
		case FLAG_ENCRYPT_USER_PASSWORD:
			if (original) {
				fr_radius_decode_password((char *)buffer, attrlen, secret, original->vector);
			} else {
				fr_radius_decode_password((char *)buffer, attrlen, secret, packet->vector);
			}
			buffer[253] = '\0';

			/*
			 *	MS-CHAP-MPPE-Keys are 24 octets, and
			 *	encrypted.  Since it's binary, we can't
			 *	look for trailing zeros.
			 */
			if (parent->flags.length) {
				if (datalen > parent->flags.length) {
					datalen = parent->flags.length;
				} /* else leave datalen alone */
			} else {
				/*
				 *	Take off trailing zeros from the END.
				 *	This allows passwords to have zeros in
				 *	the middle of a field.
				 *
				 *	However, if the password has a zero at
				 *	the end, it will get mashed by this
				 *	code.  There's really no way around
				 *	that.
				 */
				while ((datalen > 0) && (buffer[datalen - 1] == '\0')) datalen--;
			}
			break;

		/*
		 *	Tunnel-Password's may go ONLY in response
		 *	packets.  They can have a tag, so datalen is
		 *	not the same as attrlen.
		 */
		case FLAG_ENCRYPT_TUNNEL_PASSWORD:
			if (fr_radius_decode_tunnel_password(buffer, &datalen, secret,
							     original ? original->vector : nullvector) < 0) {
				goto raw;
			}
			break;

		/*
		 *  Ascend-Send-Secret
		 *  Ascend-Receive-Secret
		 */
		case FLAG_ENCRYPT_ASCEND_SECRET:
			if (!original) goto raw;
			else {
				uint8_t my_digest[AUTH_VECTOR_LEN];
				fr_radius_make_secret(my_digest, original->vector, secret, data);
				memcpy(buffer, my_digest, AUTH_VECTOR_LEN );
				buffer[AUTH_VECTOR_LEN] = '\0';
				datalen = strlen((char *) buffer);
			}
			break;

		default:
			break;
		} /* switch over encryption flags */
	}

	/*
	 *	Double-check the length after decrypting the
	 *	attribute.
	 */
	VP_TRACE("Type \"%s\" (%u)", fr_int2str(dict_attr_types, parent->type, "?Unknown?"), parent->type);
	switch (parent->type) {
	case PW_TYPE_STRING:
	case PW_TYPE_OCTETS:
		break;

	case PW_TYPE_ABINARY:
		if (datalen > sizeof(vp->vp_filter)) goto raw;
		break;

	case PW_TYPE_INTEGER:
	case PW_TYPE_IPV4_ADDR:
	case PW_TYPE_DATE:
	case PW_TYPE_SIGNED:
		if (datalen != 4) goto raw;
		break;

	case PW_TYPE_INTEGER64:
	case PW_TYPE_IFID:
		if (datalen != 8) goto raw;
		break;

	case PW_TYPE_IPV6_ADDR:
		if (datalen != 16) goto raw;
		break;

	case PW_TYPE_IPV6_PREFIX:
		if ((datalen < 2) || (datalen > 18)) goto raw;
		if (data[1] > 128) goto raw;
		break;

	case PW_TYPE_BYTE:
		if (datalen != 1) goto raw;
		break;

	case PW_TYPE_SHORT:
		if (datalen != 2) goto raw;
		break;

	case PW_TYPE_ETHERNET:
		if (datalen != 6) goto raw;
		break;

	case PW_TYPE_COMBO_IP_ADDR:
		if (datalen == 4) {
			child = fr_dict_attr_by_type(parent->vendor, parent->attr, PW_TYPE_IPV4_ADDR);
		} else if (datalen == 16) {
			child = fr_dict_attr_by_type(parent->vendor, parent->attr, PW_TYPE_IPV6_ADDR);
		} else {
			goto raw;
		}
		if (!child) goto raw;
		parent = child;	/* re-write it */
		break;

	case PW_TYPE_IPV4_PREFIX:
		if (datalen != 6) goto raw;
		if ((data[1] & 0x3f) > 32) goto raw;
		break;

		/*
		 *	The rest of the data types can cause
		 *	recursion!  Ask yourself, "is recursion OK?"
		 */

	case PW_TYPE_EXTENDED:
		if (datalen < 2) goto raw; /* etype, value */

		child = fr_dict_attr_child_by_num(parent, data[0]);
		if (!child) goto raw;
		VP_TRACE("Attr context changed %s->%s", child->name, parent->name);

		/*
		 *	Recurse to decode the contents, which could be
		 *	a TLV, IPaddr, etc.  Note that we decode only
		 *	the current attribute, and we ignore any extra
		 *	data after it.
		 */
		rcode = fr_radius_decode_pair_value(ctx, packet, original, secret, child,
						    data + 1, attrlen - 1, attrlen - 1, pvp);
		if (rcode < 0) goto raw;
		return 1 + rcode;

	case PW_TYPE_LONG_EXTENDED:
		if (datalen < 3) goto raw; /* etype, flags, value */

		child = fr_dict_attr_child_by_num(parent, data[0]);
		if (!child) {
			fr_dict_attr_t *new;

			if ((data[0] != PW_VENDOR_SPECIFIC) || (datalen < (3 + 4 + 1))) {
				/* da->attr < 255, da->vendor == 0 */
				new = fr_dict_unknown_afrom_fields(ctx, parent, 0, data[0]);
			} else {
				/*
				 *	Try to find the VSA.
				 */
				memcpy(&vendor, data + 3, 4);
				vendor = ntohl(vendor);

				if (vendor == 0) goto raw;

				new = fr_dict_unknown_afrom_fields(ctx, parent, vendor, data[7]);
			}
			child = new;

			if (!child) {
				fr_strerror_printf("%s: Internal sanity check %d", __FUNCTION__, __LINE__);
				return -1;
			}
		}
		VP_TRACE("Attr context changed %s -> %s", parent->name, child->name);

		/*
		 *	If there no more fragments, then the contents
		 *	have to be a well-known data type.
		 *
		 */
		if ((data[1] & 0x80) == 0) {
			rcode = fr_radius_decode_pair_value(ctx, packet, original, secret, child,
							    data + 2, attrlen - 2, attrlen - 2,
							    pvp);
			if (rcode < 0) goto raw;
			return 2 + rcode;
		}

		/*
		 *	This requires a whole lot more work.
		 */
		return decode_extended(ctx, packet, original, secret, child,
				       start, attrlen, packetlen, pvp);

	case PW_TYPE_EVS:
	{
		fr_dict_attr_t const *vendor_child;

		if (datalen < 6) goto raw; /* vid, vtype, value */

		if (data[0] != 0) goto raw; /* we require 24-bit VIDs */

		memcpy(&vendor, data, 4);
		vendor = ntohl(vendor);

		/*
		 *	For simplicity in our attribute tree, vendors are
		 *	represented as a subtlv(ish) of an EVS or VSA
		 *	attribute.
		 */
		vendor_child = fr_dict_attr_child_by_num(parent, vendor);
		if (!vendor_child) {
			/*
			 *	If there's no child, it means the vendor is unknown
			 *	which means the child attribute is unknown too.
			 *
			 *	fr_dict_unknown_afrom_fields will do the right thing
			 *	and create both an unknown vendor and an unknown
			 *	attr.
			 *
			 *	This can be used later by the encoder to rebuild
			 *	the attribute header.
			 */
			parent = fr_dict_unknown_afrom_fields(ctx, parent, vendor, data[4]);
			data += 5;
			datalen -= 5;
			break;
		}

		child = fr_dict_attr_child_by_num(vendor_child, data[4]);
		if (!child) {
			/*
			 *	Vendor exists but child didn't, again
			 *	fr_dict_unknown_afrom_fields will do the right thing
			 *	and only create the unknown attr.
			 */
			parent = fr_dict_unknown_afrom_fields(ctx, parent, vendor, data[4]);
			data += 5;
			datalen -= 5;
			break;
		}

		/*
		 *	Everything was found in the dictionary, we can
		 *	now recurse to decode the value.
		 */
		rcode = fr_radius_decode_pair_value(ctx, packet, original, secret, child,
						    data + 5, attrlen - 5, attrlen - 5, pvp);
		if (rcode < 0) goto raw;
		return 5 + rcode;
	}

	case PW_TYPE_TLV:
		/*
		 *	We presume that the TLVs all fit into one
		 *	attribute, OR they've already been grouped
		 *	into a contiguous memory buffer.
		 */
		rcode = fr_radius_decode_tlv(ctx, packet, original, secret, parent, data, attrlen, pvp);
		if (rcode < 0) goto raw;
		return rcode;

	case PW_TYPE_VSA:
		/*
		 *	VSAs can be WiMAX, in which case they don't
		 *	fit into one attribute.
		 */
		rcode = decode_vsa(ctx, packet, original, secret, parent, data, attrlen, packetlen, pvp);
		if (rcode < 0) goto raw;
		return rcode;

	default:
	raw:
		/*
		 *	Re-write the attribute to be "raw".  It is
		 *	therefore of type "octets", and will be
		 *	handled below.
		 */
		parent = fr_dict_unknown_afrom_fields(ctx, parent->parent, parent->vendor, parent->attr);
		if (!parent) {
			fr_strerror_printf("%s: Internal sanity check %d", __FUNCTION__, __LINE__);
			return -1;
		}
		tag = TAG_NONE;
#ifndef NDEBUG
		/*
		 *	Fix for Coverity.
		 */
		if (parent->type != PW_TYPE_OCTETS) {
			fr_dict_attr_free(&parent);
			return -1;
		}
#endif
		break;
	}

	/*
	 *	And now that we've verified the basic type
	 *	information, decode the actual data.
	 */
 alloc_cui:
	vp = fr_pair_afrom_da(ctx, parent);
	if (!vp) return -1;

	vp->vp_length = datalen;
	vp->tag = tag;

	switch (parent->type) {
	case PW_TYPE_STRING:
		p = talloc_array(vp, char, vp->vp_length + 1);
		memcpy(p, data, vp->vp_length);
		p[vp->vp_length] = '\0';
		vp->vp_strvalue = p;
		break;

	case PW_TYPE_OCTETS:
		fr_pair_value_memcpy(vp, data, vp->vp_length);
		break;

	case PW_TYPE_ABINARY:
		if (vp->vp_length > sizeof(vp->vp_filter)) {
			vp->vp_length = sizeof(vp->vp_filter);
		}
		memcpy(vp->vp_filter, data, vp->vp_length);
		break;

	case PW_TYPE_BYTE:
		vp->vp_byte = data[0];
		break;

	case PW_TYPE_SHORT:
		vp->vp_short = (data[0] << 8) | data[1];
		break;

	case PW_TYPE_INTEGER:
		memcpy(&vp->vp_integer, data, 4);
		vp->vp_integer = ntohl(vp->vp_integer);
		break;

	case PW_TYPE_INTEGER64:
		memcpy(&vp->vp_integer64, data, 8);
		vp->vp_integer64 = ntohll(vp->vp_integer64);
		break;

	case PW_TYPE_DATE:
		memcpy(&vp->vp_date, data, 4);
		vp->vp_date = ntohl(vp->vp_date);
		break;

	case PW_TYPE_ETHERNET:
		memcpy(vp->vp_ether, data, 6);
		break;

	case PW_TYPE_IPV4_ADDR:
		memcpy(&vp->vp_ipaddr, data, 4);
		break;

	case PW_TYPE_IFID:
		memcpy(vp->vp_ifid, data, 8);
		break;

	case PW_TYPE_IPV6_ADDR:
		memcpy(&vp->vp_ipv6addr, data, 16);
		break;

	case PW_TYPE_IPV6_PREFIX:
		/*
		 *	FIXME: double-check that
		 *	(vp->vp_octets[1] >> 3) matches vp->vp_length + 2
		 */
		memcpy(vp->vp_ipv6prefix, data, vp->vp_length);
		if (vp->vp_length < 18) {
			memset(((uint8_t *)vp->vp_ipv6prefix) + vp->vp_length, 0,
			       18 - vp->vp_length);
		}
		break;

	case PW_TYPE_IPV4_PREFIX:
		/* FIXME: do the same double-check as for IPv6Prefix */
		memcpy(vp->vp_ipv4prefix, data, vp->vp_length);

		/*
		 *	/32 means "keep all bits".  Otherwise, mask
		 *	them out.
		 */
		if ((data[1] & 0x3f) > 32) {
			uint32_t addr, mask;

			memcpy(&addr, vp->vp_octets + 2, sizeof(addr));
			mask = 1;
			mask <<= (32 - (data[1] & 0x3f));
			mask--;
			mask = ~mask;
			mask = htonl(mask);
			addr &= mask;
			memcpy(vp->vp_ipv4prefix + 2, &addr, sizeof(addr));
		}
		break;

	case PW_TYPE_SIGNED:	/* overloaded with vp_integer */
		memcpy(&vp->vp_integer, buffer, 4);
		vp->vp_integer = ntohl(vp->vp_integer);
		break;

	default:
		fr_pair_list_free(&vp);
		fr_strerror_printf("%s: Internal sanity check %d", __FUNCTION__, __LINE__);
		return -1;
	}
	vp->type = VT_DATA;
	*pvp = vp;

	return attrlen;
}


/** Create a "normal" VALUE_PAIR from the given data
 *
 */
ssize_t fr_radius_decode_pair(TALLOC_CTX *ctx,
			      RADIUS_PACKET *packet, RADIUS_PACKET const *original,
			      char const *secret,
			      fr_dict_attr_t const *parent, uint8_t const *data, size_t length,
			      VALUE_PAIR **pvp)
{
	ssize_t rcode;

	fr_dict_attr_t const *da;

	if ((length < 2) || (data[1] < 2) || (data[1] > length)) {
		fr_strerror_printf("%s: Insufficient data", __FUNCTION__);
		return -1;
	}

	da = fr_dict_attr_child_by_num(parent, data[0]);
	if (!da) {
		VP_TRACE("Unknown attribute %u", data[0]);
		da = fr_dict_unknown_afrom_fields(ctx, parent, 0, data[0]);
	}
	if (!da) return -1;
	VP_TRACE("Attr context changed %s -> %s",da->parent->name, da->name);

	/*
	 *	Pass the entire thing to the decoding function
	 */
	if (da->flags.concat) {
		VP_TRACE("Concat attribute", __FUNCTION__);
		return decode_concat(ctx, da, data, length, pvp);
	}

	/*
	 *	Note that we pass the entire length, not just the
	 *	length of this attribute.  The Extended or WiMAX
	 *	attributes may have the "continuation" bit set, and
	 *	will thus be more than one attribute in length.
	 */
	rcode = fr_radius_decode_pair_value(ctx, packet, original, secret, da,
					    data + 2, data[1] - 2, length - 2, pvp);
	if (rcode < 0) return rcode;

	return 2 + rcode;
}
