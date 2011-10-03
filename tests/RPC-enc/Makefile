
include Makefile.common

FILES = client.c server.c lib.c lib.h lib_proxy.c net.c net.h rpc-enc.h  Makefile proxies.conf RPC-enc.v iml.all.good.txt query.in pvmodel.good.txt

execute: $(P1) $(P2)
	./$(P1) $(P1_CMD) & \
	sleep 1; ./$(P2) $(P2_CMD) & \
	wait

logs: compile # $(P1) $(P2)
	./$(P1) $(P1_CMD) > server.log & \
	sleep 1; ./$(P2) $(P2_CMD) > client.log &\
	wait

csec-verify-log: csec-verify.log
csec-verify.log:
	$(MAKE) -f Makefile.csec-tools iml verify > $@ 2>&1

$(P1) $(P2): polarssl gcm $(P1_SRC)
	$(CC) $(DFLAGS) -Wall $(INCS) $(P1_SRC) $(LIBLOCS) $(LIBS) -o $(P1)
	$(CC) $(DFLAGS) -Wall $(INCS) $(P2_SRC) $(LIBLOCS) $(LIBS) -o $(P2)

compile: $(P1) $(P2)

polarssl: polarssl/library/libminimal.a

polarssl/library/libminimal.a:
	cd polarssl/library; make minimal

gcm: gcm/libgcm.a

gcm/libgcm.a:
	cd gcm; make gcmlib

boogie:
	vcc /3 /t /p:/I"polarssl/include" client.c

boogiecheck: boogie
	boogie "C:\Program Files\Microsoft Research\Vcc\Headers\Vcc3Prelude.bpl" client.bpl

typecheck:
	vcc /3 /p:/I"gcm" /p:/I"polarssl/include" server.c

everything: compile sym
everything: iml verify


all: compile sym

zip: boogie
	tar -czf release.tgz $(FILES)

clean:
	$(RM) $(P1) $(P2)
	$(MAKE) -f Makefile.csec-tools clean

purge:: clean
	cd polarssl/library; make clean
	cd gcm; make clean
