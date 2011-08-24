cmake_minimum_required(VERSION 2.6)

project (csec-tools)

# set(CMAKE_VERBOSE_MAKEFILE true)

set(CSEC_ROOT ${CMAKE_BINARY_DIR})

# 32 or 64 bit?

if(CMAKE_SYSTEM_PROCESSOR MATCHES ".*64.*")
  # set(64_BIT true)
  set(OPENSSL_CONFIG csec-64)
else()
  # set(64_BIT false)
  set(OPENSSL_CONFIG csec)
endif(CMAKE_SYSTEM_PROCESSOR MATCHES ".*64.*")

######## deps/CIL ################################

set(CIL_ROOT ${CSEC_ROOT}/deps/cil-1.3.7-svn)

# find ARCHOS as configured by CIL
if(NOT EXISTS ${CIL_ROOT}/config.mk)
  execute_process(COMMAND ./configure WORKING_DIRECTORY ${CIL_ROOT})
endif(NOT EXISTS ${CIL_ROOT}/config.mk)

execute_process(COMMAND sed -n "s/.*ARCHOS=\\(.*\\)/\\1/p" ${CIL_ROOT}/config.mk
                OUTPUT_VARIABLE ARCHOS
                OUTPUT_STRIP_TRAILING_WHITESPACE)
                
#configure_file (mk/archos.mk.in mk/archos.mk)
# execute_process(COMMAND make -sf mk/archos.mk
#                 OUTPUT_VARIABLE ARCHOS 
#                 OUTPUT_STRIP_TRAILING_WHITESPACE)

set(CIL_OBJDIR ${CIL_ROOT}/obj/${ARCHOS})
set(CIL_LIB ${CIL_OBJDIR}/cil.a)
set(CILLY ${CIL_ROOT}/bin/cilly)

add_custom_command(OUTPUT ${CIL_ROOT}/Makefile
                     COMMAND ./configure
                     WORKING_DIRECTORY ${CIL_ROOT}
                     VERBATIM)

add_custom_command(OUTPUT ${CIL_LIB} 
                     COMMAND make
                     DEPENDS ${CIL_ROOT}/Makefile
                     WORKING_DIRECTORY ${CIL_ROOT}
                     VERBATIM)

######## deps/ocamlyices ###########################

set(OCAMLYICES_ROOT ${CSEC_ROOT}/deps/ocamlyices)
set(OCAMLYICES ${OCAMLYICES_ROOT}/ocamlyices.cmxa ${OCAMLYICES_ROOT}/yices.cmi)

add_custom_command(OUTPUT ${OCAMLYICES_ROOT}/Makefile
                     COMMAND ./configure
                     WORKING_DIRECTORY ${OCAMLYICES_ROOT}
                     VERBATIM)

add_custom_command(OUTPUT ${OCAMLYICES}
                    COMMAND make
                    DEPENDS ${OCAMLYICES_ROOT}/Makefile
                    WORKING_DIRECTORY ${OCAMLYICES_ROOT}
                    VERBATIM)

######## deps/openssl ###########################

set(OPENSSL ${CSEC_ROOT}/deps/openssl-1.0.0d)

add_custom_command(OUTPUT ${OPENSSL}/Makefile
                    COMMAND ./Configure ${OPENSSL_CONFIG}
                    WORKING_DIRECTORY ${OPENSSL}
                    VERBATIM)

add_custom_command(OUTPUT ${OPENSSL}/libcrypto.a ${OPENSSL}/libssl.a 
                    COMMAND make clean
                    COMMAND make 
                    DEPENDS ${OPENSSL}/Makefile
                    WORKING_DIRECTORY ${OPENSSL}
                    VERBATIM)

######## deps/openssl-crestified ###########################

set(OPENSSL_CRESTIFIED ${CSEC_ROOT}/deps/openssl-1.0.0d-crestified)

add_custom_command(OUTPUT ${OPENSSL_CRESTIFIED}/Makefile
                    COMMAND ./Configure ${OPENSSL_CONFIG}
                    WORKING_DIRECTORY ${OPENSSL_CRESTIFIED}
                    VERBATIM)

add_custom_command(OUTPUT ${OPENSSL_CRESTIFIED}/libcrypto_sym.a ${OPENSSL_CRESTIFIED}/libssl_sym.a 
                    COMMAND make clean
                    COMMAND make -f ${CSEC_ROOT}/mk/openssl.mk sym
                    DEPENDS ${OPENSSL_CRESTIFIED}/Makefile
                    WORKING_DIRECTORY ${OPENSSL_CRESTIFIED}
                    VERBATIM)

######## deps/cryptoverif ###########################

set(CV_ROOT ${CSEC_ROOT}/deps/cryptoverif1.11)

set(CRYPTOVERIF ${CV_ROOT}/cryptoverif)

add_custom_command(OUTPUT ${CRYPTOVERIF}
                    COMMAND ./build
                    WORKING_DIRECTORY ${CV_ROOT}
                    VERBATIM)

######## deps/proverif ###########################

set(PV_ROOT ${CSEC_ROOT}/deps/proverif1.84)

set(PROVERIF ${PV_ROOT}/proverif)

add_custom_command(OUTPUT ${PROVERIF}
                    COMMAND ./build
                    WORKING_DIRECTORY ${PV_ROOT}
                    VERBATIM)


######## proxies ##############################

set(PROXIES ${CSEC_ROOT}/proxies)
set(LIBSSL_PROXY_SYM ${PROXIES}/libssl_proxy_sym.a)

add_custom_command(OUTPUT ${LIBSSL_PROXY_SYM}
                    COMMAND make
                    WORKING_DIRECTORY ${PROXIES}
                    DEPENDS ${CIL_LIB}
                    VERBATIM)

######## include ################################

set(HEADERS include/crest.h include/proxies/common.h include/proxies/interface.h
            include/proxies/openssl-proxies-1.0.0.h
            include/proxies/openssl-proxies.h)

# include/proxies/openssl-proxies-0.9.8o.h 

set(HEADERS_ORIG 
            ${PROXIES}/crest.h  ${PROXIES}/common.h  ${PROXIES}/interface.h
            ${PROXIES}/openssl_proxies-1.0.0.h
            ${PROXIES}/openssl_proxies.h)

# ${PROXIES}/openssl_proxies-0.9.8o.h  

list(LENGTH HEADERS NUM_HEADERS)
math(EXPR NUM_HEADERS "${NUM_HEADERS} - 1")

foreach(I RANGE ${NUM_HEADERS})

  list(GET HEADERS ${I} HEADER)
  list(GET HEADERS_ORIG ${I} HEADER_ORIG)
  add_custom_command(OUTPUT ${HEADER}
                      COMMAND cp ${HEADER_ORIG} ${HEADER}
                      DEPENDS ${HEADER_ORIG}
                      VERBATIM)

endforeach(I RANGE NUM_HEADERS)

add_custom_target(include 
                    DEPENDS ${HEADERS})
                    
######## src/CIL ##############################

add_custom_target(src_CIL 
                    COMMAND make
                    DEPENDS ${CIL_ROOT}/Makefile
                    WORKING_DIRECTORY src/CIL
                    VERBATIM)

######## src/symtrace ##############################

set(IMLTRACE ${CSEC_ROOT}/src/symtrace/imltrace)
set(PITRACE  ${CSEC_ROOT}/src/symtrace/pitrace)

add_custom_command(OUTPUT ${IMLTRACE} ${PITRACE}
                    COMMAND make
                    DEPENDS ${OCAMLYICES_ROOT}/ocamlyices.cmxa
                    WORKING_DIRECTORY src/symtrace/
                    VERBATIM)

add_custom_target(src_symtrace 
                    COMMAND make
                    WORKING_DIRECTORY src/CIL
                    VERBATIM)
                    
######## tests ##############################

# ${OPENSSL_CRESTIFIED}/libcrypto_sym.a ${OPENSSL_CRESTIFIED}/libssl_sym.a
set(TEST_DEPS ${HEADERS} ${OPENSSL}/libcrypto.a ${OPENSSL}/libssl.a  
               ${OCAMLYICES} ${LIBSSL_PROXY_SYM} ${IMLTRACE} ${PITRACE} ${PROVERIF})
               
######## tests/simple_hash ##############################

set(SIMPLE_HASH tests/simple_hash)

add_custom_target(simple_hash ALL
                    COMMAND make
                    DEPENDS ${TEST_DEPS}
                    WORKING_DIRECTORY ${SIMPLE_HASH}
                    VERBATIM)

add_custom_target(simple_hash_check
                    COMMAND make check
                    DEPENDS ${TEST_DEPS}
                    WORKING_DIRECTORY ${SIMPLE_HASH}
                    VERBATIM)

######## tests/RPC ##############################

set(RPC tests/RPC)

add_custom_target(RPC ALL
                    COMMAND make
                    DEPENDS ${TEST_DEPS}
                    WORKING_DIRECTORY ${RPC}
                    VERBATIM)

add_custom_target(RPC_check
                    COMMAND make check
                    DEPENDS ${TEST_DEPS}
                    WORKING_DIRECTORY ${RPC}
                    VERBATIM)


######## tests/CSur ##############################

set(CSUR tests/CSur)

add_custom_target(CSur ALL
                    COMMAND make
                    DEPENDS ${TEST_DEPS}
                    WORKING_DIRECTORY ${CSUR}
                    VERBATIM)

add_custom_target(CSur_check
                    COMMAND make check
                    DEPENDS ${TEST_DEPS}
                    WORKING_DIRECTORY ${CSUR}
                    VERBATIM)

######## tests/NSL ##############################

set(NSL tests/NSL)

add_custom_target(NSL ALL
                    COMMAND make
                    DEPENDS ${TEST_DEPS}
                    WORKING_DIRECTORY ${NSL}
                    VERBATIM)

add_custom_target(NSL_check
                    COMMAND make check
                    DEPENDS ${TEST_DEPS}
                    WORKING_DIRECTORY ${NSL}
                    VERBATIM)

######## check ##############################

add_custom_target(check)

add_dependencies(check simple_hash_check RPC_check CSur_check NSL_check)

######## clean ##############################

# Not cleaning in dependencies:
# ${CIL_ROOT} ${OPENSSL} ${PV_ROOT}
set(CLEAN_DIRS ${OCAMLYICES_ROOT} ${PROXIES} src/CIL src/symtrace ${RPC} ${SIMPLE_HASH} ${CSUR} ${NSL})

set(i 1)

add_custom_target(cleanup)

foreach(DIR ${CLEAN_DIRS})

  math(EXPR i "${i} + 1")

  string(REPLACE "/" "_" SUFFIX ${DIR})

  # I wish COMMENT would be shown in make help too
  add_custom_target(cleanup_${i}
                      COMMAND make clean
                      COMMENT make clean in ${DIR}
                      WORKING_DIRECTORY ${DIR})

  add_dependencies(cleanup cleanup_${i})

endforeach(DIR)
 
######## CONFIG ##############################

configure_file (mk/common.mk.in mk/common.mk)
