android.ml: a.out
	./a.out $(ANDROID_PLATFORM)/android.jar > $@

a.out: gen.ml
	ocamlfind ocamlc -package "javalib" -linkpkg gen.ml
