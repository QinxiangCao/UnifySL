unifysl_dir := ..
dst_dir		:= ./demo
coq_exe		:= coqc
coq_flags	:= -R $(unifysl_dir) Logic
src         := GenInterface.v
dst         := $(dst_dir)/Generated.v

.PHONY: all clean

all: $(dst)

Utils.vo: Utils.v
	$(coq_exe) $(coq_flags) Utils.v

Config.vo: Config.v Utils.vo
	$(coq_exe) $(coq_flags) Config.v

$(dst): $(src) Utils.vo Config.vo
	$(coq_exe) $(coq_flags) $(src) > $@

test: $(dst)
	$(coq_exe) $(coq_flags) $(dst_dir)/Shallow.v

clean:
	@rm -rf *.vo *.glob .*.aux $(dst) 2>/dev/null
