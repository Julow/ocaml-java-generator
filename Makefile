OCAMLOPT = ocamlfind ocamlopt
OCAMLOPT_FLAGS =
DEPENDENCIES = -package "javalib" -linkpkg

all: android.ml

android.ml: a.out
	CLASSES="android.view.View android.inputmethodservice.InputMethodService"; \
	./a.out $(ANDROID_PLATFORM)/android.jar $$CLASSES > $@

a.out: gen.ml
	$(OCAMLOPT) $(OCAMLOPT_FLAGS) $(DEPENDENCIES) -o $@ $<

clean:
	rm -f a.out android.ml
	rm -f gen.o gen.cmo gen.cmx gen.cmi

re: clean
	make all

.PHONY: all clean re
