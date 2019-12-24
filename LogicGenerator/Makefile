unifysl_dir := ..
dst_dir		:= ./demo
coq_exe		:= coqc
coq_flags	:= -R $(unifysl_dir) Logic
src         := Generate.v
dst         := $(dst_dir)/Generated.v

.PHONY: all clean

all: $(dst)

Config.vo: Config.v
	$(coq_exe) $(coq_flags) Config.v

$(dst): $(src) Config.vo
	$(coq_exe) $(coq_flags) $(src) > $@

test: $(dst)
	$(coq_exe) $(coq_flags) $(dst_dir)/Shallow.v

clean:
	@rm -rf *.vo *.glob .*.aux $(dst) 2>/dev/null
