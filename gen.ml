
let string_ends_with str ends =
	let len_str = String.length str
	and len_ends = String.length ends in
	len_str >= len_ends
	&& ends = String.sub str (len_str - len_ends) len_ends

let option_to_list =
	function Some v -> [ v ] | None -> []

(** Returns a new string with
	each occurence of `search` replaced by `replace` *)
let string_replace_char search replace =
	String.map (fun c -> if c = search then replace else c)

open Javalib_pack
open Javalib
open JBasics

exception Fail of string * string

(** Returns the class's name and list of dependencies
	A dependency can be:
		- super class
		- interfaces
		- method argument/return type
		- field type *)
let get_deps =
	let rec value_type_deps =
		function
		| TBasic _					-> []
		| TObject (TClass cls_name)	-> [ cls_name ]
		| TObject (TArray vt)		-> value_type_deps vt
	in

	let method_deps methodmap =
		MethodMap.fold (fun sigt _ deps ->
			List.fold_left (fun deps d -> value_type_deps d @ deps) deps
				(option_to_list (ms_rtype sigt) @ ms_args sigt)
		) methodmap []
	in

	let field_deps fieldmap =
		FieldMap.fold (fun sigt _ deps ->
			value_type_deps (fs_type sigt) @ deps
		) fieldmap []
	in

	let interface_deps intf =
		List.sort_uniq cn_compare @@
		intf.i_interfaces
		@ field_deps intf.i_fields
		@ method_deps intf.i_methods
	in

	let class_deps cls =
		List.sort_uniq cn_compare @@
		option_to_list cls.c_super_class
		@ cls.c_interfaces
		@ field_deps cls.c_fields
		@ method_deps cls.c_methods
	in
	function
	| JInterface intf	-> intf.i_name, interface_deps intf
	| JClass cls		-> cls.c_name, class_deps cls

let indent =
	List.map (fun line -> "\t" ^ line)

(** Generates a list of recursive classes
	First generates a function for each static fields
	finally the classes
	Final non-Object static fields are constant *)
let rec generate_chunk_of_class classes =

	let (~%) = Printf.sprintf in

	(** Returns the JNI signature from a `value_type` *)
	let rec jni_sigt =
		function
		| TBasic `Bool			-> "Z"
		| TBasic `Byte			-> "B"
		| TBasic `Char			-> "C"
		| TBasic `Double		-> "D"
		| TBasic `Float			-> "F"
		| TBasic `Int			-> "I"
		| TBasic `Long			-> "J"
		| TBasic `Short			-> "S"
		| TObject (TArray t)	-> "[" ^ jni_sigt t
		| TObject (TClass cls)	->
			"L" ^ string_replace_char '.' '/' (cn_name cls) ^ ";"
	in

	let jni_meth_sigt sigt =
		let args =
			ms_args sigt
			|> List.map jni_sigt
			|> String.concat ""
		and ret =
			match ms_rtype sigt with
			| Some t -> jni_sigt t
			| None -> "V" in
		~% "(%s)%s" args ret
	in

	(** For a type, returns:
		(arg function, call function, ocaml type) *)
	let ocaml_java_conv =
		function
		| TBasic `Bool		-> "arg_bool",		"call_bool",	"bool"
		| TBasic `Byte		-> "arg_int8",		"call_int8",	"int"
		| TBasic `Char		-> "arg_char",		"call_char",	"char"
		| TBasic `Double	-> "arg_double",	"call_double",	"float"
		| TBasic `Float		-> "arg_float",		"call_float",	"float"
		| TBasic `Int		-> "arg_int",		"call_int",		"int"
		| TBasic `Long		-> "arg_int64",		"call_int64",	"int64"
		| TBasic `Short		-> "arg_int16",		"call_int16",	"int"
		| TObject (TClass cn) when cn_name cn = "java.lang.String"
							-> "arg_string",	"call_string",	"string"
		| TObject _			-> "arg_obj",		"call_obj",		"obj"
	in

	let (@@@) (a, b) (a', b') = a @ a', b @ b' in
	let separate (a, b) =
		let s = (function [] -> [] | l -> "" :: l) in
		s a, s b
	in

	let module_name cls_name =
		cn_simple_name cls_name
			|> String.map (function '.' | '$' -> '_' | c -> c)
	in

	let class_name = module_name in

	(* ==== *)
	(* Generate a class *)
	(* generating function are expected to returns the pair:
		(list of mli lines, list of ml lines) *)

	let class_ alloc =
		let ocaml_java_conv =
			function
			| TObject (TClass cn)	->
				"arg_obj @@ to_obj",
				"of_obj_unsafe @@ call_obj",
				~% "_ %s.t" (module_name cn)
			| t						-> ocaml_java_conv t
		in

		let ocaml_java_conv_rtype =
			function
			| Some t	->
				let _, call, t = ocaml_java_conv t in
				call, t
			| None		-> "call_unit", "unit"
		in

		let static_field sigt =
			let final ocaml_type value =
				let fname = fs_name sigt in
				[ ~% "val %s : %s" fname ocaml_type ],
				[ ~% "let %s = %s" fname value ]
			in
			function
			| Some (ConstString s)	-> final "string" (~% "\"%s\"" (jstr_pp s))
			| Some (ConstInt v)		-> final "int" (Int32.to_string v)
			| Some (ConstFloat v)	-> final "float" (string_of_float v)
			| Some (ConstLong v)	-> final "int64" (Int64.to_string v)
			| Some (ConstDouble v)	-> final "float" (string_of_float v)
			| Some (ConstClass _)
			| None					->
				let name = fs_name sigt
				and type_ = fs_type sigt in
				let fid = alloc (`Field_static (name, jni_sigt type_)) in
				let _, call_func, ocaml_type = ocaml_java_conv type_ in
				[	~% "val %s : unit -> %s" name ocaml_type ],
				[	~% "let %s () =" name;
					~% "	field_static _cls %s;" fid;
					~% "	%s ()" call_func ]
		in

		let field sigt =
			let name = fs_name sigt
			and type_ = fs_type sigt in
			let fid = alloc (`Field (name, jni_sigt type_)) in
			let _, call_func, ocaml_type = ocaml_java_conv type_ in
			[	~% "val %s : _ t -> %s" name ocaml_type ],
			[	~% "let %s obj =" name;
				~% "	field obj %s;" fid;
				~% "	%s ()" call_func ]
		in

		(** OCaml type of a method *)
		let meth_type sigt =
			let args = ms_args sigt |> function
				| []	-> "unit"
				| args	->
					String.concat " -> " @@
					List.map (fun vt ->
						let _, _, t = ocaml_java_conv vt in t) args
			in
			let _, rtype = ocaml_java_conv_rtype (ms_rtype sigt) in
			~% "%s -> %s" args rtype
		in

		let meth alloc s_val s_let s_meth sigt =
			let name = ms_name sigt |>
				function "<init>" -> "init_" | n -> n in
			let args = ms_args sigt in
			let arg_names =
				String.concat " " @@
				List.mapi (fun i _ -> ~% "a%d" i) args
			in
			let meth_id = alloc name (jni_meth_sigt sigt) in
			let call_func, _ = ocaml_java_conv_rtype (ms_rtype sigt) in
			[	s_val name (meth_type sigt) ],
			[	s_let name arg_names;
				s_meth meth_id ]
			@ List.mapi (fun i arg ->
					let arg_func, _, _ = ocaml_java_conv arg in
					~% "	%s a%d;" arg_func i
				) args @
			[	~% "	%s ()" call_func ]
		in

		let static_meth =
			meth (fun name sigt -> alloc (`Meth_static (name, sigt)))
				~% "val %s : %s"
				~% "let %s %s ="
				~% "	meth_static _cls %s;"
		and meth =
			meth (fun name sigt -> alloc (`Meth (name, sigt)))
				~% "val %s : _ t -> %s"
				~% "let %s obj %s ="
				~% "	meth obj %s;"
		in

		let abstract_meth =
			function
			| { am_synthetic = true }
			| { am_access = `Protected }	-> [], []
			| { am_signature = s }			-> meth s
		in
		let concrete_meth =
			function
			| { cm_synthetic = true }
			| { cm_access = (`Protected | `Private) }	-> [], []
			| { cm_signature = s } when ms_name s = "<clinit>"	-> [], []
			| { cm_static = true; cm_signature = s }	-> static_meth s
			| { cm_signature = s; _ }					-> meth s
		in

		function
		| JInterface intf	->
			MethodMap.fold (fun _ m acc ->
				abstract_meth m @@@ acc
			) intf.i_methods ([], [])
			|> separate
			|> FieldMap.fold (fun sigt if_ acc ->
				static_field sigt if_.if_value
				@@@ acc
			) intf.i_fields
		| JClass cls		->
			MethodMap.fold (fun _ ->
				function
				| AbstractMethod am -> (@@@) (abstract_meth am)
				| ConcreteMethod cm -> (@@@) (concrete_meth cm)
			) cls.c_methods ([], [])
			|> separate
			|> FieldMap.fold (fun sigt cf acc ->
				(if cf.cf_static
					then static_field sigt cf.cf_value
					else field sigt)
				@@@ acc
			) cls.c_fields
	in

	let globals =
		List.map (fun (id, value) ->
			let init =
				function
				| `Field_static (name, sigt)	->
					~% "get_field_static _cls \"%s\" \"%s\"" name sigt
				| `Field (name, sigt)			->
					~% "get_field \"%s\" \"%s\"" name sigt
				| `Meth_static (name, sigt)		->
					~% "get_meth_static _cls \"%s\" \"%s\"" name sigt
				| `Meth (name, sigt)			->
					~% "get_meth \"%s\" \"%s\"" name sigt
			in
			~% "let %s = %s" id (init value)
		)
	in

	let class_ begin_ cls_or_intf =

		let next_id = ref 1
		and gbls = ref [] in

		let alloc value =
			let ids = ~% "_%d" !next_id in
			incr next_id;
			gbls := (ids, value) :: !gbls;
			ids
		in

		let cls_name, dependencies = get_deps cls_or_intf in
		let mli, ml = class_ alloc cls_or_intf in

		let types =
			[	~% "type t' = [ %s ]" @@
					String.concat " | " @@
					List.map (fun n -> "`" ^ class_name n) @@
					cls_name :: dependencies;
				~% "type 'a t = ([> t' ] as 'a) obj" ]
		in

		print_endline @@
		String.concat "\n" @@
			[ ~% "%s %s : sig" begin_ (module_name cls_name) ]
			@ indent types
			@ [ "" ]
			@ indent mli
			@ [ ""
				"	val of_obj : Java.obj -> t' obj";
				"";
				"end = struct" ]
			@ indent types
			@ [ "";
				~% "	let _cls = find_class \"%s\"" (cn_name cls_name) ]
			@ indent (globals !gbls)
			@ [ "" ]
			@ indent ml
			@ [ "";
				"	let of_obj o = of_obj _cls o";
				"" ]
			@ [ "end" ]

	in

	List.iter print_endline [
		"type 'a obj constraint 'a = [>]";
		"";
		"external to_obj : 'a obj -> Java.obj = \"%identity\"";
		"";
		"external of_obj_unsafe : Java.obj -> 'a obj = \"%identity\"";
		"";
		"let of_obj cls obj =";
		"	if instanceof obj cls then failwith(\"of_obj\");";
		"	of_obj_unsafe obj";
		""
	];

	match classes with
	| []		-> ()
	| h :: tl	->
		class_ "module rec" h;
		List.iter (class_ "and") tl

(** Returns a table containing the jclass and name of dependencies
	of the classes in `jar_file` and their dependencies *)
let classes_with_deps jar_file =
	let tbl = Hashtbl.create 100 in
	iter (fun cls_or_intf ->
		let name, deps = get_deps cls_or_intf in
		Hashtbl.add tbl name (cls_or_intf, deps);
	) jar_file;
	tbl

(* Dummy implementation that ignore dependencies
	and put every classes in a single chunk
	(it's a bit complex and is almost useless here
	since there is a lot of cicle in dependencies) *)
let reorder_by_deps clss =
	[ Hashtbl.fold (fun _ (cls, _) lst -> cls :: lst) clss [] ]

let () =
	(if Array.length Sys.argv <= 1 then failwith "Missing argument");
	prerr_endline "begin";
	let clss = classes_with_deps Sys.argv.(1) in
	prerr_endline "classes_with_deps";
	let clss = reorder_by_deps clss in
	prerr_endline "reorder_by_deps";
	List.iter generate_chunk_of_class clss;
	prerr_endline "done"
