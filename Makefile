BENCHMARK_FILES:=$(wildcard tests/hu-benchmarks/length*.smt2) $(wildcard tests/hu-benchmarks/indexof-*.smt2)
JAR_FILE:=target/scala-2.11/ostrich-assembly-1.0.jar
BASELINE_JAR:=baseline.jar
BENCHMARK_CMD:="java -jar ${JAR_FILE} -useparikh {file}"
comma:= ,
empty:=
space:= $(empty) $(empty)

benchmark.md: ${JAR_FILE} ${BENCHMARK_FILES}
	hyperfine \
		--export-markdown $@ \
		--ignore-failure \
		--warmup 1 \
		--parameter-list file $(subst $(space),$(comma),$(BENCHMARK_FILES))  \
		-- "java ${JAVAOPTS} -jar ${JAR_FILE} -useparikh {file}"

.PHONY: compare
compare: ${BASELINE_JAR} ${JAR_FILE}
	for file in ${BENCHMARK_FILES} ; do \
		hyperfine \
			--warmup 1 \
			--parameter-list jarfile ${JAR_FILE},baseline.jar  \
			-- "java ${JAVAOPTS} -jar {jarfile} -useparikh $$file" ; \
	done

.PHONY: new-baseline
new-baseline:
	cp ${JAR_FILE} ${BASELINE_JAR}


%.pdf: %.dot
	dot -Tpdf  -Efontsize=9.0 -o $@ $<
