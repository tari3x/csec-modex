#include <stdlib.h>
#include <stdio.h>
#include <string.h>

#include <openssl/ssl.h>

#include "RPC.h"

// #define VERBOSE

void client(dstr_c *a, dstr_c *b, key_c *k, dstr_c *s)
{
	channel_c *c;
	dbytes_c *mac, pload2, mac2;
	dstr_c *t;
#ifdef VERBOSE
	unsigned long i;
#endif

#ifdef CSEC_VERIFY
	readenv(s->address, &(s->length), "request");
	event1("client_begin", s->address, s->length);
#endif

	c = socket_connect();

	mac = hmacsha1(k, request(s));
	send(c, concat(utf8(s), mac));
#ifdef VERBOSE
	printf("Sent request\n");
	for(i = 0; i < s->length; i++)
		printf("%02x", s->address[i]);
	printf("\nwith MAC\n");
	for (i = 0; i < 20; i++)
		printf("%02x", (unsigned char) mac->address[i]);
	printf("\n");
#endif

	iconcat(recv(c), &pload2, &mac2);
	t = iutf8(&pload2);
	hmacsha1Verify(k, response(s, t), &mac2);
#ifdef VERBOSE
	printf("Received and authenticated response\n");
	for(i = 0; i < t->length; i++)
		printf("%02x", t->address[i]);
	printf("\nwith MAC\n");
	for (i = 0; i < 20; i++)
		printf("%02x", (unsigned char) mac2.address[i]);
	printf("\n");
#endif

#ifdef CSEC_VERIFY
	event2("client_accept", s->address, s->length, t->address, t->length);
#endif
}

void server(dstr_c *a, dstr_c *b, key_c *k)
{
	channel_c *c;
	dbytes_c pload, mac, *mac2;
	dstr_c *s, *t;
#ifdef VERBOSE
	unsigned long i;
#endif

	c = socket_listen();

	iconcat(recv(c), &pload, &mac);
	s = iutf8(&pload);
	hmacsha1Verify(k, request(s), &mac);
#ifdef VERBOSE
	printf("Received and authenticated request\n");
	for(i = 0; i < s->length; i++)
		printf("%02x", s->address[i]);
	printf("\nwith MAC\n");
	for (i = 0; i < 20; i++)
		printf("%02x", (unsigned char) mac.address[i]);
	printf("\n");
#endif

	t = service(s);

#ifdef CSEC_VERIFY
	readenv(t->address, &(t->length), "response");
	event2("server_reply", s->address, s->length, t->address, t->length);
#endif

	mac2 = hmacsha1(k, response(s, t));
	send(c, concat(utf8(t), mac2));
#ifdef VERBOSE
	printf("Sent response\n");
	for(i = 0; i < t->length; i++)
		printf("%02x", t->address[i]);
	printf("\nwith MAC\n");
	for (i = 0; i < 20; i++)
		printf("%02x", (unsigned char) mac2->address[i]);
	printf("\n");
#endif

	// wait for the client to close, to avoid "Address already in use" errors
	wait_close(c);
}

int main(int argc, char *argv[])
{
	key_c *k;
	dstr_c *alice, *bob, *s;

	if (argc < 2)
	{
		fprintf(stderr, "Wrong command-line arguments.\n");
		return 1;
	}

	SSL_load_error_strings();
  
	alice = str(fromString("Alice", 5));
	bob = str(fromString("Bob", 3));

	k = fromString("ThisIsASharedKey", 16);
#ifdef CSEC_VERIFY
	readenv(k->address, &(k->length), "keyAB");
#endif

	s = str(fromString("ThisIsAPayload", 14));

	// FIXME: make it properly
	int isClient = 0;

#ifdef CSEC_VERIFY
	mute();
#endif
	isClient = !strncmp(argv[1], "client", 6);
#ifdef CSEC_VERIFY
	unmute();
#endif

	if (isClient)
	{
		client(alice, bob, k, s);
	}
	else // if (!strncmp(argv[1], "server", 6))
	{
		server(alice ,bob, k);
	}
	/* else
	{
		fprintf(stderr, "Wrong command-line arguments.\n");
		return 1;
	} */

	return 0;
}
