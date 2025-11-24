(* This is the user facing AST of moo. 
 * The variables should be converted into using de Brujin indices
 * by a first pass before further execution. *)
module Surface = struct
  module Type = struct
    type type_schema =
      | Base of string
      | Kind of string * string list

    type abstract_type =
      | Var of string
      | Neg of abstract_type

    type type_expr =
      | Name of string
      | PosProd of type_use list
      | NegProd of type_use list
      | KindInstantiation of string * type_use list
      | Forall of string * type_use
      | Exists of string * type_use

    and type_use =
      | Abstract of abstract_type
      | Instantiated of polar_type

    and polar_type =
      | Plus of type_expr
      | Minus of type_expr

    module Show = struct
      let show_type_schema ts =
        match ts with
        | Base s -> s
        | Kind (k, params) -> Printf.sprintf "(%s %s)" k (String.concat " " params)
      ;;

      let rec show_abstract_type at =
        match at with
        | Var s -> s
        | Neg at' -> Printf.sprintf "~%s" (show_abstract_type at')
      ;;

      let rec show_type_expr te =
        match te with
        | Name s -> s
        | PosProd tus ->
          let tuple_string = tus |> List.map show_type_use |> String.concat " * " in
          Printf.sprintf "(%s)" tuple_string
        | NegProd tus ->
          let cotuple_string = tus |> List.map show_type_use |> String.concat " & " in
          Printf.sprintf "(%s)" cotuple_string
        | KindInstantiation (k, args) ->
          Printf.sprintf "(%s %s)" k (String.concat " " (List.map show_type_use args))
        | Forall (at, tu) -> Printf.sprintf "(forall %s. %s)" at (show_type_use tu)
        | Exists (at, tu) -> Printf.sprintf "(exists %s. %s)" at (show_type_use tu)

      and show_type_use tu =
        match tu with
        | Abstract at -> show_abstract_type at
        | Instantiated pt -> show_polar_type pt

      and show_polar_type pt =
        match pt with
        | Plus te -> Printf.sprintf "%s+" (show_type_expr te)
        | Minus te -> Printf.sprintf "%s-" (show_type_expr te)
      ;;
    end
  end

  type name =
    { name : string
    ; typ : Type.type_use option
    }

  type producer =
    | Mu of name * cut
    | Tuple of neutral list
    | Codone
    | Cosplit of name list * cut
    | Gen of string * neutral
    | Pack of Type.type_expr * Type.type_use * neutral

  and consumer =
    | MuTilde of name * cut
    | Split of name list * cut
    | Cotuple of neutral list
    | Done
    | Inst of Type.type_expr * Type.type_use * neutral
    | Unpack of string * neutral

  and cut =
    { p : neutral
    ; c : neutral
    }

  and neutral =
    | Name of string
    | Positive of producer
    | Negative of consumer

  type definition =
    | Producer of name * producer
    | Consumer of name * consumer
    | TypeDef of Type.type_schema * Type.type_expr

  type t =
    { definitions : definition list
    ; main : cut
    }

  (* Surface's show should look exactly like the code.
   * but Core will look closer to product-mu-mu calculus.
   *)
  module Show = struct
    let show_name n =
      match n.typ with
      | None -> n.name
      | Some typ -> Printf.sprintf "[%s : %s]" n.name (Type.Show.show_type_use typ)
    ;;

    let rec show_producer p =
      match p with
      | Mu (coname, cut) ->
        Printf.sprintf "(letcc %s -> %s)" (show_name coname) (show_cut cut)
      | Tuple xs ->
        let tuple_string = xs |> List.map show_neutral |> String.concat ", " in
        Printf.sprintf "(%s)" tuple_string
      | Cosplit (xs, cut) ->
        let names_string = xs |> List.map show_name |> String.concat ", " in
        Printf.sprintf "(cosplit '(%s) -> %s)" names_string (show_cut cut)
      | Codone -> "codone"
      | Gen (at, p) -> Printf.sprintf "(gen %s. %s)" at (show_neutral p)
      | Pack (pt, at, p) ->
        Printf.sprintf
          "(pack [%s] %s. %s)"
          (Type.Show.show_type_expr pt)
          (Type.Show.show_type_use at)
          (show_neutral p)

    and show_consumer c =
      match c with
      | MuTilde (name, cut) ->
        Printf.sprintf "(let %s -> %s)" (show_name name) (show_cut cut)
      | Split (xs, cut) ->
        let names_string = xs |> List.map show_name |> String.concat ", " in
        Printf.sprintf "(split (%s) -> %s)" names_string (show_cut cut)
      | Cotuple xs ->
        let cotuple_string = xs |> List.map show_neutral |> String.concat ", " in
        Printf.sprintf "'(%s)" cotuple_string
      | Done -> "done"
      | Inst (pt, at, c) ->
        Printf.sprintf
          "(inst [%s] %s. %s)"
          (Type.Show.show_type_expr pt)
          (Type.Show.show_type_use at)
          (show_neutral c)
      | Unpack (at, c) -> Printf.sprintf "(unpack %s. %s)" at (show_neutral c)

    and show_cut (cut : cut) =
      Printf.sprintf "[%s %s]" (show_neutral cut.p) (show_neutral cut.c)

    and show_neutral n =
      match n with
      | Name n -> n
      | Positive p -> show_producer p
      | Negative c -> show_consumer c
    ;;

    let show_definition def =
      match def with
      | Producer (name, body) ->
        Printf.sprintf "defp %s = %s;;" (show_name name) (show_producer body)
      | Consumer (name, body) ->
        Printf.sprintf "defc %s = %s;;" (show_name name) (show_consumer body)
      | TypeDef (schema, expr) ->
        Printf.sprintf
          "type %s = %s;;"
          (Type.Show.show_type_schema schema)
          (Type.Show.show_type_expr expr)
    ;;

    let show t =
      let defs_str = String.concat "\n" (List.map show_definition t.definitions) in
      let main_str = show_cut t.main in
      if defs_str = "" then main_str else Printf.sprintf "%s\n\n%s" defs_str main_str
    ;;
  end

  module Producer = struct
    let mu coname cut = Mu (coname, cut)
    let tuple xs = Tuple xs
    let cosplit xs cut = Cosplit (xs, cut)
    let codone = Codone
    let gen at p = Gen (at, p)
    let pack pt at p = Pack (pt, at, p)
  end

  module Consumer = struct
    let mutilde name cut = MuTilde (name, cut)
    let split xs cut = Split (xs, cut)
    let cotuple xs = Cotuple xs
    let done_ = Done
    let inst pt at c = Inst (pt, at, c)
    let unpack at c = Unpack (at, c)
  end

  module Neutral = struct
    let identifier name = Name name
  end

  let make_name (ident : string) (typ : Type.type_use option) = { name = ident; typ }
  let defp (name : name) (input : name) (body : cut) = Producer (name, Mu (input, body))

  let defc (name : name) (input : name) (body : cut) =
    Consumer (name, MuTilde (input, body))
  ;;

  let cut p c = { p; c }
  let program definitions main = { definitions; main }
end

(* Core AST uses de Brujin indices for bound variables/covariables.
 * 
 * Both names and conames are converted to de Brujin indices, sharing
 * a single binding environment. Each binder (μ, μ̃, cosplit, split) 
 * introduces variables at indices 0, 1, etc., with outer bindings
 * shifted accordingly.
 * 
 * eg. (letcc x ... x ... (let p ... x p ...)) -> (letcc ... 0 ... (let ... 1 0 ...)) *)
module Core = struct
  module Type = struct
    type type_schema =
      | Base of string
      | Kind of string * int (* the number of abstract types in the kind shape *)

    type abstract_type =
      | Var of int (* abstract type de Brujin index *)
      | Neg of abstract_type

    type type_expr =
      | Name of string
      | PosProd of type_use list
      | NegProd of type_use list
      | KindInstantiation of string * type_use list
      | Forall of
          int
          * type_use (* both of these introduce 1 abstract type usage, should be aware *)
      | Exists of int * type_use

    and type_use =
      | Abstract of abstract_type
      | Instantiated of polar_type

    and polar_type =
      | Plus of type_expr
      | Minus of type_expr

    module Show = struct
      let show_type_schema ts =
        match ts with
        | Base s -> s
        | Kind (k, n) ->
          let abstract_types = List.init n (fun i -> Printf.sprintf "a%d" i) in
          Printf.sprintf "(%s %s)" k (String.concat " " abstract_types)
      ;;

      let rec show_abstract_type at =
        match at with
        | Var i -> Printf.sprintf "a%d" i
        | Neg at' -> Printf.sprintf "~%s" (show_abstract_type at')
      ;;

      let rec show_type_expr te =
        match te with
        | Name s -> s
        | PosProd tus ->
          let tuple_string = tus |> List.map show_type_use |> String.concat " * " in
          Printf.sprintf "(%s)" tuple_string
        | NegProd tus ->
          let cotuple_string = tus |> List.map show_type_use |> String.concat " & " in
          Printf.sprintf "(%s)" cotuple_string
        | KindInstantiation (k, args) ->
          Printf.sprintf "(%s %s)" k (String.concat " " (List.map show_type_use args))
        | Forall (ivar, t) -> Printf.sprintf "(forall %d . %s)" ivar (show_type_use t)
        | Exists (ivar, t) -> Printf.sprintf "(exists %d . %s)" ivar (show_type_use t)

      and show_type_use tu =
        match tu with
        | Abstract at -> show_abstract_type at
        | Instantiated pt -> show_polar_type pt

      and show_polar_type pt =
        match pt with
        | Plus te -> Printf.sprintf "%s+" (show_type_expr te)
        | Minus te -> Printf.sprintf "%s-" (show_type_expr te)
      ;;
    end
  end

  type identifier =
    | Free of string
    | Bound of int * Type.type_use option

  (* the debrujin index conversion will lose us the type information of the bound variables, 
   * so we leave them in the producer and consumer *)
  type producer =
    | Mu of cut * Type.type_use option
    | Tuple of neutral list
    | Cosplit of cut * Type.type_use option list
    | Codone
    | Gen of string * neutral
    | Pack of Type.type_expr * Type.type_use * neutral

  and consumer =
    | MuTilde of cut * Type.type_use option
    | Split of cut * Type.type_use option list
    | Cotuple of neutral list
    | Done
    | Inst of Type.type_expr * Type.type_use * neutral
    | Unpack of string * neutral

  and cut =
    { p : neutral
    ; c : neutral
    }

  and neutral =
    | Name of identifier
    | Positive of producer
    | Negative of consumer

  type definition =
    | Producer of string * producer
    | Consumer of string * consumer
    | TypeDef of Type.type_schema * Type.type_expr

  type t =
    { definitions : definition list
    ; main : cut
    }

  module Show = struct
    let show_identifier name =
      match name with
      | Free name -> name
      | Bound (n, typ) ->
        (match typ with
         | None -> string_of_int n
         | Some t -> Printf.sprintf "[%d : %s]" n (Type.Show.show_type_use t))
    ;;

    let rec show_producer p =
      match p with
      | Mu (cut, _) -> Printf.sprintf "(μ.%s)" (show_cut cut)
      | Tuple xs ->
        let tuple_string = xs |> List.map show_neutral |> String.concat ", " in
        Printf.sprintf "(%s)" tuple_string
      | Cosplit (cut, typs) ->
        let typ_string =
          typs |> List.length |> fun n -> List.init n string_of_int |> String.concat ", "
        in
        Printf.sprintf "('(%s).%s)" typ_string (show_cut cut)
      | Codone -> "codone"
      | Gen (at, p) -> Printf.sprintf "(gen %s. %s)" at (show_neutral p)
      | Pack (pt, at, p) ->
        Printf.sprintf
          "(pack [%s] %s. %s)"
          (Type.Show.show_type_expr pt)
          (Type.Show.show_type_use at)
          (show_neutral p)

    and show_consumer c =
      match c with
      | MuTilde (cut, _) -> Printf.sprintf "(μ̃.%s)" (show_cut cut)
      | Split (cut, typs) ->
        let typ_string =
          typs |> List.length |> fun n -> List.init n string_of_int |> String.concat ", "
        in
        Printf.sprintf "((%s).%s)" typ_string (show_cut cut)
      | Cotuple xs ->
        let cotuple_string = xs |> List.map show_neutral |> String.concat ", " in
        Printf.sprintf "'(%s)" cotuple_string
      | Done -> "done"
      | Inst (pt, at, c) ->
        Printf.sprintf
          "(inst [%s] %s. %s)"
          (Type.Show.show_type_expr pt)
          (Type.Show.show_type_use at)
          (show_neutral c)
      | Unpack (at, c) -> Printf.sprintf "(unpack %s. %s)" at (show_neutral c)

    and show_cut (cut : cut) =
      Printf.sprintf "<%s|%s>" (show_neutral cut.p) (show_neutral cut.c)

    and show_neutral n =
      match n with
      | Name n -> show_identifier n
      | Positive p -> show_producer p
      | Negative c -> show_consumer c
    ;;

    let show_definition def =
      match def with
      | Producer (name, body) -> Printf.sprintf "defp %s = %s;;" name (show_producer body)
      | Consumer (name, body) -> Printf.sprintf "defc %s = %s;;" name (show_consumer body)
      | TypeDef (schema, expr) ->
        Printf.sprintf
          "type %s = %s;;"
          (Type.Show.show_type_schema schema)
          (Type.Show.show_type_expr expr)
    ;;

    let show t =
      let defs_str = String.concat "\n" (List.map show_definition t.definitions) in
      let main_str = show_cut t.main in
      if defs_str = "" then main_str else Printf.sprintf "%s\n\n%s" defs_str main_str
    ;;
  end

  module Converter = struct
    module S = Surface

    module TypeConverter = struct
      module ST = S.Type
      module T = Type

      (* the set of type variables. *)
      type abstract_type_env = string list

      let empty_abstract_type_env () : abstract_type_env = []
      let add_type (ty_env : abstract_type_env) name : abstract_type_env = name :: ty_env

      let get_type (ty_env : abstract_type_env) name =
        let index = List.length ty_env - 1 in
        let rec aux lst name current_index =
          match lst with
          | [] -> failwith (Printf.sprintf "unbound abstract type: %s" name)
          | hd :: tl ->
            if String.equal hd name then current_index else aux tl name (current_index - 1)
        in
        aux ty_env name index
      ;;

      let abstract_type_env_of_kind (kind_shape : ST.type_schema) : abstract_type_env =
        match kind_shape with
        | ST.Kind (_, abstract_types) ->
          (* we get to do this because schemas can only be defined at top-level.
           * at top-level, we don't expect any available abstract types, that
           * are introduced from ie forall or exists. *)
          List.fold_left
            (fun acc at_name -> add_type acc at_name)
            (empty_abstract_type_env ())
            abstract_types
        | ST.Base _ -> empty_abstract_type_env ()
      ;;

      let convert_schema schema =
        match schema with
        | ST.Base s -> T.Base s
        | ST.Kind (k, n) -> T.Kind (k, List.length n)
      ;;

      let rec convert_abstract_type (abstract_type_env : abstract_type_env) abstract_type =
        match abstract_type with
        | ST.Var s -> T.Var (get_type abstract_type_env s)
        | ST.Neg at -> T.Neg (convert_abstract_type abstract_type_env at)

      and convert_type_expr (abstract_type_env : abstract_type_env) type_expr =
        match type_expr with
        | ST.Name s -> T.Name s
        | ST.PosProd tus ->
          let tus' = List.map (convert_type_use abstract_type_env) tus in
          T.PosProd tus'
        | ST.NegProd tus ->
          let tus' = List.map (convert_type_use abstract_type_env) tus in
          T.NegProd tus'
        | ST.KindInstantiation (k, args) ->
          T.KindInstantiation (k, List.map (convert_type_use abstract_type_env) args)
        | ST.Forall (at, tu) ->
          let abstract_type_env' = add_type abstract_type_env at in
          let next_num = get_type abstract_type_env' at in
          T.Forall (next_num, convert_type_use abstract_type_env' tu)
        | ST.Exists (at, tu) ->
          let abstract_type_env' = add_type abstract_type_env at in
          let next_num = get_type abstract_type_env' at in
          T.Exists (next_num, convert_type_use abstract_type_env' tu)

      and convert_type_use (abstract_type_env : abstract_type_env) use =
        match use with
        | ST.Abstract at -> T.Abstract (convert_abstract_type abstract_type_env at)
        | ST.Instantiated pt -> T.Instantiated (convert_polar_type abstract_type_env pt)

      and convert_polar_type (abstract_type_env : abstract_type_env) polar_type =
        match polar_type with
        | ST.Plus te -> T.Plus (convert_type_expr abstract_type_env te)
        | ST.Minus te -> T.Minus (convert_type_expr abstract_type_env te)
      ;;
    end

    type term_env = (string * Type.type_use option) list

    (* represents the list of abstract types introduced at run time *)
    type type_env = TypeConverter.abstract_type_env

    let name_match = String.equal
    let empty_term_env () : term_env = []
    let empty_type_env = TypeConverter.empty_abstract_type_env

    let lookup_identifier env n =
      let rec aux stack n depth =
        match stack with
        | [] -> Free n (* free variables have no type info *)
        | (n', typ) :: stack' ->
          if name_match n n' then Bound (depth, typ) else aux stack' n (depth + 1)
      in
      aux env n 0
    ;;

    let convert_binder_type (binder : S.name) =
      let abstract_type_env = TypeConverter.empty_abstract_type_env () in
      Option.map
        (fun typ -> TypeConverter.convert_type_use abstract_type_env typ)
        binder.typ
    ;;

    let push_names (vs : S.name list) (env : term_env) =
      List.map (fun (s : S.name) -> s.name, convert_binder_type s) vs @ env
    ;;

    let binders_are_unique xs =
      let uniques = List.sort_uniq compare xs in
      List.length xs = List.length uniques
    ;;

    let rec convert_producer (term_env : term_env) (type_env : type_env) p : producer =
      match p with
      | S.Mu (k, cut) ->
        Mu (convert_cut (push_names [ k ] term_env) type_env cut, convert_binder_type k)
      | S.Tuple xs ->
        let xs' = List.map (convert_neutral term_env type_env) xs in
        Tuple xs'
      | S.Cosplit (names, cut) ->
        if not (binders_are_unique names)
        then raise (Failure "Cosplit: name conflict in parameters")
        else (
          let term_env' = push_names names term_env in
          Cosplit (convert_cut term_env' type_env cut, List.map convert_binder_type names))
      | S.Codone -> Codone
      | S.Gen (at, p) ->
        let type_env' = TypeConverter.add_type type_env at in
        Gen (at, convert_neutral term_env type_env' p)
      | S.Pack (pt, at, p) ->
        let pt' = TypeConverter.convert_type_expr type_env pt in
        let at' = TypeConverter.convert_type_use type_env at in
        Pack (pt', at', convert_neutral term_env type_env p)

    and convert_consumer (term_env : term_env) (type_env : type_env) c : consumer =
      match c with
      | S.MuTilde (v, cut) ->
        MuTilde
          (convert_cut (push_names [ v ] term_env) type_env cut, convert_binder_type v)
      | S.Split (names, cut) ->
        if not (binders_are_unique names)
        then raise (Failure "Split: name conflict in parameters")
        else (
          let term_env' = push_names names term_env in
          Split (convert_cut term_env' type_env cut, List.map convert_binder_type names))
      | S.Cotuple xs ->
        let xs' = List.map (convert_neutral term_env type_env) xs in
        Cotuple xs'
      | S.Done -> Done
      | S.Inst (pt, at, c) ->
        let pt' = TypeConverter.convert_type_expr type_env pt in
        let at' = TypeConverter.convert_type_use type_env at in
        Inst (pt', at', convert_neutral term_env type_env c)
      | S.Unpack (at, c) ->
        let type_env' = TypeConverter.add_type type_env at in
        Unpack (at, convert_neutral term_env type_env' c)

    and convert_cut (term_env : term_env) (type_env : type_env) cut : cut =
      { p = convert_neutral term_env type_env cut.p
      ; c = convert_neutral term_env type_env cut.c
      }

    and convert_neutral (term_env : term_env) (type_env : type_env) neutral : neutral =
      match neutral with
      | S.Name n -> Name (lookup_identifier term_env n)
      | S.Positive p -> Positive (convert_producer term_env type_env p)
      | S.Negative c -> Negative (convert_consumer term_env type_env c)
    ;;

    (* definitions are evaluated without environment *)
    let convert_definition definition : definition =
      match definition with
      | S.Producer (n, p) ->
        Producer (n.name, convert_producer (empty_term_env ()) (empty_type_env ()) p)
      | S.Consumer (cn, c) ->
        Consumer (cn.name, convert_consumer (empty_term_env ()) (empty_type_env ()) c)
      | S.TypeDef (schema, expr) ->
        let type_env = TypeConverter.abstract_type_env_of_kind schema in
        let schema = TypeConverter.convert_schema schema in
        let expr = TypeConverter.convert_type_expr type_env expr in
        TypeDef (schema, expr)
    ;;
  end

  let convert (t : Surface.t) : t =
    { definitions = List.map Converter.convert_definition t.definitions
    ; main =
        Converter.convert_cut
          (Converter.empty_term_env ())
          (Converter.empty_type_env ())
          t.main
    }
  ;;
end
