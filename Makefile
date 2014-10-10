include Modules

Sources := $(Modules:%=%.v)

.DEFAULT_GOAL := all

all : Coq_Make
	$(MAKE) -f Coq_Make all

clean : Coq_Make
	$(MAKE) -f Coq_Make clean; rm -rf Coq_Make

Coq_Make: Makefile Modules $(Sources)
	coq_makefile -install none -opt -o Coq_Make -R . Categories $(Sources)

.PHONY : clean all