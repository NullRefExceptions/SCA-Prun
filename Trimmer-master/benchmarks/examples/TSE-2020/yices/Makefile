YICES=yices
YICES_BITCODE=${YICES}_main.bc
YICES_VERSION=2.6.1
YICES_NAME=${YICES}-${YICES_VERSION}
YICES_TAR=${YICES_NAME}.tar.gz

YICES_MANIFEST=${YICES}.manifest
YICES_PATCH=${YICES}.patch

OUT_DIR?=trimmer
LOG_FILE?=logs

BITCODE_WRAPPER?=wllvm
BITCODE_EXTRACT?=extract-bc

all: ${YICES_BITCODE}

compress: ${OUT_DIR} ${YICES_BITCODE}
	cp ${YICES_BITCODE} ${OUT_DIR}
	cp libyices.a ${OUT_DIR} && \
	cd ${OUT_DIR} && \
	echo '{"binary": "yices_main_fin", "native_libs":[],"name": "yices_main", "args": ["--logic=QF_AUFBV", "abc.ys"], "modules": [], "ldflags": ["-lgmp","libyices.a"], "main": "yices_main.bc", "config_files": []}' > ${YICES_MANIFEST} && \
	python ${TRIMMER_HOME}/tool/trimmer.py ${YICES_MANIFEST} work_dir $(option) 2> ${LOG_FILE} 

${YICES_BITCODE}: ${YICES_NAME}
	cp ${YICES_PATCH} ${YICES_NAME} && \
	cd ${YICES_NAME} && \
	patch -p1 -f -R -i ./${YICES_PATCH} && \
	sed -i 's/gcc/wllvm -fno-inline -fno-inline-functions -Xclang -disable-O0-optnone/g' src/Makefile && \
	CC=${BITCODE_WRAPPER} make && \
	${BITCODE_EXTRACT} build/x86_64-pc-linux-gnu-release/bin/${YICES}_main && \
	mv build/x86_64-pc-linux-gnu-release/bin/${YICES_BITCODE} ../ && \
	cp build/x86_64-pc-linux-gnu-release/lib/libyices.a ../

test_yices:
	@echo "\t\tTest Yices"
	cp abc.ys ${OUT_DIR}/work_dir/ && \
	${OUT_DIR}/work_dir/yices_main_fin_stripped > t_out && \
	${YICES_NAME}/build/x86_64-pc-linux-gnu-release/bin/yices_main --logic=QF_AUFBV abc.ys > o_out
	@echo "Output comparison to Baseline:"
	@cmp -s ./t_out o_out; \
	RETVAL=$$?; \
	if [ $$RETVAL -eq 0 ]; then \
		echo "\tyices test baseline compare? Passed!"; \
	else \
		echo "\tyices test baseline compare? Failed!"; \
	fi
	@rm ./o_out
	@rm ./t_out

		
${OUT_DIR}:
	mkdir -p ${OUT_DIR}

${YICES_NAME}:
	tar -xvzf ./${YICES_TAR}

base:
	opt -O3 ${YICES_BITCODE} -o ${YICES}_opt.bc
	llc -filetype=obj ${YICES}_opt.bc -o ${YICES}_opt.o
	clang++ -O3 ${YICES}_opt.o -lgmp libyices.a -o ${YICES}_bin 
	strip ${YICES}_bin -o ${YICES}_base_stripped

clean:
	-rm -r ${YICES_NAME}
	-rm *.bc *.a
	-rm -r ${OUT_DIR}
	-rm *_bin *_stripped *.o
