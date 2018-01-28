
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

	let prefix_uppercase s =
		if s.[0] = Char.uppercase_ascii s.[0]
		then "_" ^ s
		else s
	in

	(* ==== *)
	(* Generate a class *)
	(* generating function are expected to returns the pair:
		(list of mli lines, list of ml lines) *)

	let class_ alloc =
		(** For a type, returns:
			(camljava perfix, ocaml type) *)
		let rec ocaml_java_conv =
			function
			| TBasic `Bool			-> "bool",		"bool"
			| TBasic `Byte			-> "byte",		"int"
			| TBasic `Char			-> "char",		"char"
			| TBasic `Double		-> "double",	"float"
			| TBasic `Float			-> "float",		"float"
			| TBasic `Int			-> "int",		"int"
			| TBasic `Long			-> "long",		"int64"
			| TBasic `Short			-> "short",		"int"
			| TObject (TArray a)	->
				"array",	snd (ocaml_java_conv a) ^ " jarray"
			| TObject (TClass cn) when cn_name cn = "java.lang.String"
									-> "string",	"string"
			| TObject (TClass cn) when cn_name cn = "java.lang.Object"
									-> "object",	"obj"
			| TObject (TClass cn)	->
				"obj_unsafe", ~% "_ %s.t" (module_name cn)
		in

		let ocaml_java_conv_rtype =
			function
			| Some t	-> ocaml_java_conv t
			| None		-> "void", "unit"
		in

		let static_field_get name prefix ocaml_type fid =
			[	~% "val get'%s : unit -> %s" name ocaml_type ],
			[	~% "let get'%s () =" name;
				~% "	read_field_static_%s _cls %s" prefix fid ]
		in

		let static_field sigt =
			let name = fs_name sigt
			and type_ = fs_type sigt in
			let fid = alloc (`Field_static (name, jni_sigt type_)) in
			let prefix, ocaml_type = ocaml_java_conv type_ in
			static_field_get name prefix ocaml_type fid @@@ (
			[	~% "val set'%s : %s -> unit" name ocaml_type ],
			[	~% "let set'%s v =" name;
				~% "	write_field_static_%s _cls %s v" prefix fid ])
		in

		let static_final_field sigt =
			let name = fs_name sigt
			and type_ = fs_type sigt in
			let fid = alloc (`Field_static (name, jni_sigt type_)) in
			let prefix, ocaml_type = ocaml_java_conv type_ in
			static_field_get name prefix ocaml_type fid
		in

		let static_final_field sigt =
			let final ocaml_type value =
				let name = prefix_uppercase (fs_name sigt) in
				[ ~% "val %s : %s" name ocaml_type ],
				[ ~% "let %s = %s" name value ]
			in
			function
			| Some (ConstString s)	-> final "string" (~% "\"%s\"" (jstr_pp s))
			| Some (ConstInt v)		-> final "int" (Int32.to_string v)
			| Some (ConstFloat v)	-> final "float" (string_of_float v)
			| Some (ConstLong v)	-> final "int64" (Int64.to_string v)
			| Some (ConstDouble v)	-> final "float" (string_of_float v)
			| Some (ConstClass _)
			| None					-> static_final_field sigt
		in

		let field_get sigt =
			let name = fs_name sigt
			and type_ = fs_type sigt in
			let fid = alloc (`Field (name, jni_sigt type_)) in
			let prefix, ocaml_type = ocaml_java_conv type_ in
			[	~% "val get'%s : _ t -> %s" name ocaml_type ],
			[	~% "let get'%s obj =" name;
				~% "	read_field_%s obj %s" prefix fid ]
		in

		let field_set sigt =
			let name = fs_name sigt
			and type_ = fs_type sigt in
			let fid = alloc (`Field (name, jni_sigt type_)) in
			let prefix, ocaml_type = ocaml_java_conv type_ in
			[	~% "val set'%s : _ t -> %s -> unit" name ocaml_type ],
			[	~% "let set'%s obj v =" name;
				~% "	write_field_%s obj %s v" prefix fid ]
		in

		(** OCaml type of a method *)
		let meth_args_type =
			function
			| []		-> "unit"
			| args		->
				String.concat " -> " @@
				List.map (fun vt -> snd (ocaml_java_conv vt)) args
		in
		let meth_type sigt =
			let args = meth_args_type (ms_args sigt) in
			let _, rtype = ocaml_java_conv_rtype (ms_rtype sigt) in
			~% "%s -> %s" args rtype
		in

		let arg_name = ~% "a%d" in
		let arg_names =
			function
			| []		-> "()"
			| args		->
				String.concat " " @@
				List.mapi (fun i _ -> arg_name i) args
		in

		let push_calls =
			List.mapi (fun i arg ->
				let prefix, _ = ocaml_java_conv arg in
				~% "	push_%s %s;" prefix (arg_name i)
			)
		in

		let static_meth sigt =
			let name, args = ms_name sigt, ms_args sigt in
			let meth_id = alloc (`Meth_static (name, (jni_meth_sigt sigt))) in
			let prefix, _ = ocaml_java_conv_rtype (ms_rtype sigt) in
			`Meth_static (prefix_uppercase name, sigt, fun name ->
				[	~% "val %s : %s" name (meth_type sigt) ],
				[	~% "let %s %s =" name (arg_names args) ]
				@ push_calls args @
				[	~% "	call_static_%s _cls %s" prefix meth_id ])
		in

		let meth sigt =
			let name, args = ms_name sigt, ms_args sigt in
			let meth_id = alloc (`Meth (name, (jni_meth_sigt sigt))) in
			let prefix, _ = ocaml_java_conv_rtype (ms_rtype sigt) in
			`Meth (prefix_uppercase name, sigt, fun name ->
				[	~% "val %s : _ t -> %s" name (meth_type sigt) ],
				[	~% "let %s obj %s =" name (arg_names args) ]
				@ push_calls args @
				[	~% "	call_%s obj %s" prefix meth_id ])
		in

		let constructor sigt =
			let args = ms_args sigt in
			let meth_id = alloc (`Constructor (jni_meth_sigt sigt)) in
			`Constructor ("new'", sigt, fun name ->
				[	~% "val %s : %s -> t' obj" name (meth_args_type args) ],
				[	~% "let %s %s =" name (arg_names args) ]
				@ push_calls args @
				[	~% "	of_obj_unsafe (new_ _cls %s)" meth_id ])
		in

		let abstract_meth =
			function
			| { am_synthetic = true }
			| { am_access = `Protected }	-> `Ignore
			| { am_signature = s }			-> meth s
		and concrete_meth =
			function
			| { cm_synthetic = true }
			| { cm_access = (`Protected | `Private) }			-> `Ignore
			| { cm_signature = s } when ms_name s = "<clinit>"	-> `Ignore
			| { cm_signature = s } when ms_name s = "<init>"	-> constructor s
			| { cm_static = true; cm_signature = s }			-> static_meth s
			| { cm_signature = s; _ }							-> meth s
		in

		(** Check for name collision and generate unique suffix
			then call the function generating the code and concat them
			`meths` is a list of (name * sigt * (name -> result)) *)
		let resolve_collision meths =
			let rec mangle = function
				| TBasic `Bool			-> "B"
				| TBasic `Byte			-> "Y"
				| TBasic `Char			-> "C"
				| TBasic `Double		-> "D"
				| TBasic `Float			-> "F"
				| TBasic `Int			-> "I"
				| TBasic `Long			-> "L"
				| TBasic `Short			-> "H"
				| TObject (TArray t)	-> "A" ^ mangle t
				| TObject (TClass cls) when cn_name cls = "java.lang.String"
										-> "S"
				| TObject (TClass cls) when cn_name cls = "java.lang.Object"
										-> "O"
				| TObject (TClass cls)	-> cn_simple_name cls
			in
			let mangle sigt =
				String.concat "" @@
				List.map mangle @@
				ms_args sigt
			in

			List.fold_left (fun acc -> function
				| []					-> acc
				| [ (name, _, render) ]	-> render name @@@ acc
				| meths					->
					List.fold_left (fun acc (name, sigt, render) ->
						render (name ^ mangle sigt) @@@ acc) acc meths
			) ([], []) @@
			List.fold_left (fun lst (name, _, _ as m) ->
				match lst with
				| ((name', _, _) :: _ as col) :: tl when name = name' ->
					(m :: col) :: tl
				| lst	-> [ m ] :: lst
			) [] @@
			List.stable_sort
				(fun (a_name, a_sigt, _) (b_name, b_sigt, _) ->
					let (&&&) a b = if a = 0 then b else a in
					compare a_name b_name &&& ms_compare a_sigt b_sigt)
				meths
		in

		(** Split the result of `abstract_meth` and `concrete_meth` in 3 lists:
				static methods, constructors, methods
			The order of the methods is reversed *)
		let split_method_kinds meths =
			List.fold_left (fun (sm, cm, mm) m ->
				match m with
				| `Meth_static m	-> (m :: sm, cm, mm)
				| `Constructor c	-> (sm, c :: cm, mm)
				| `Meth m			-> (sm, cm, m :: mm)
				| `Ignore			-> (sm, cm, mm)
			) ([], [], []) meths
		in

		(** split_method_kinds, resolve_collision and concat *)
		let split_and_resolve_collision meths =
			let sm, cm, mm = split_method_kinds meths in
			separate (resolve_collision mm)
			@@@ separate (resolve_collision cm)
			@@@ resolve_collision sm
		in

		function
		| JInterface intf	->
			MethodMap.fold (fun _ m acc -> abstract_meth m :: acc)
				intf.i_methods []
			|> split_and_resolve_collision
			|> separate
			|> FieldMap.fold (fun sigt if_ acc ->
					static_final_field sigt if_.if_value @@@ acc
				) intf.i_fields
		| JClass cls		->
			MethodMap.fold (fun _ m acc ->
				match m with
				| AbstractMethod am -> abstract_meth am :: acc
				| ConcreteMethod cm -> concrete_meth cm :: acc
			) cls.c_methods []
			|> split_and_resolve_collision
			|> separate
			|> FieldMap.fold (fun sigt cf acc ->
				(@@@) acc @@
				match cf with
				| { cf_synthetic = true }
				| { cf_access = (`Default | `Private | `Protected) } ->
					[], []
				| { cf_static = true; cf_kind = Final; cf_value } ->
					static_final_field sigt cf_value
				| { cf_static = true } ->
					static_field sigt
				| { cf_kind = Final } ->
					field_get sigt
				| _ ->
					field_get sigt @@@ field_set sigt
			) cls.c_fields
	in

	let globals =
		List.map (fun (id, value) ->
			let init =
				function
				| `Field_static (name, sigt)	->
					~% "get_field_static _cls \"%s\" \"%s\"" name sigt
				| `Field (name, sigt)			->
					~% "get_field _cls \"%s\" \"%s\"" name sigt
				| `Meth_static (name, sigt)		->
					~% "get_meth_static _cls \"%s\" \"%s\"" name sigt
				| `Meth (name, sigt)			->
					~% "get_meth _cls \"%s\" \"%s\"" name sigt
				| `Constructor sigt				->
					~% "get_constructor _cls \"%s\"" sigt
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
			[	~% "(* %s *)" (cn_name cls_name);
				~% "%s %s : sig" begin_ (module_name cls_name) ]
			@ indent types
			@ [ "" ]
			@ indent mli
			@ [	"";
				"	val of_obj : Java.obj -> t' obj";
				"";
				"end = struct" ]
			@ indent types
			@ [	"";
				~% "	let _cls = find_class \"%s\"" (cn_name cls_name) ]
			@ indent (globals !gbls)
			@ [ "" ]
			@ indent ml
			@ [	"";
				"	let of_obj o = of_obj _cls o";
				"" ]
			@ [ "end" ]

	in

	List.iter print_endline [
		"open Java";
		"open Jclass";
		"";
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
