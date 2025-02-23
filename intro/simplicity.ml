(* Groupoid Infinity Simplicity HoTT as Rezk/GAP replacement

   $ ocamlopt -o simplicity simplicity.ml

   Copyright (c) 2025 Groupoid Infinity

   STATUS: early bird prototype (achieved 20 rewrites)
*)


type type_name = Simplex | Group | Simplicial | Chain | Category | Monoid
type superscript = S1 | S2 | S3 | S4 | S5 | S6 | S7 | S8 | S9

type term =
  | Id of string                  (* e.g., a *)
  | Comp of term * term           (* e.g., a ∘ b *)
  | Inv of term                   (* e.g., a^-1 *)
  | Pow of term * superscript     (* e.g., a³ *)
  | E                             (* identity: e *)

type constrain =
  | Eq of term * term             (* e.g., a ∘ a = e *)
  | Map of string * string list   (* e.g., ∂₁ < [e01; e02; e12] *)

type hypothesis =
  | Decl of string list * type_name  (* e.g., (a b c : Simplex) *)
  | Equality of string * term * term  (* e.g., ac = ab ∘ bc *)
  | Mapping of string * term * term   (* e.g., ∂₁ = C₂ < C₃ *)

type rank = Finite of int | Infinite  (* Updated to support ∞ *)

type type_def = {
  name : string;
  typ : type_name;
  context : hypothesis list;
  rank : rank;                  (* <n> *)
  elements : string list;       (* <elements> *)
  faces : string list option;   (* Optional: only for Simplex *)
  constraints : constrain list (* <constraints> *)
}

(* Parsing helpers *)
let parse_superscript = function
  | "¹" -> S1 | "²" -> S2 | "³" -> S3 | "⁴" -> S4 | "⁵" -> S5
  | "⁶" -> S6 | "⁷" -> S7 | "⁸" -> S8 | "⁹" -> S9 | _ -> failwith "Invalid superscript"

let parse_n s = match s with
  | "∞" -> Infinite
  | n -> Finite (int_of_string n)

(* Type checking algorithm *)
let check_type_def defn =
  let env = Hashtbl.create 10 in  (* Environment for declared identifiers *)
  
  (* Check context *)
  List.iter (fun h ->
    match h with
    | Decl (ids, typ) ->
        List.iter (fun id ->
          if Hashtbl.mem env id then failwith ("Duplicate declaration: " ^ id)
          else Hashtbl.add env id typ
        ) ids
    | Equality (id, t1, t2) ->
        Hashtbl.add env id Simplex (* Assume Simplex for now *)
    | Mapping (id, t1, t2) ->
        Hashtbl.add env id Simplex (* Assume Simplex for maps *)
  ) defn.context;
  
  (* Check elements *)
  List.iter (fun el ->
    if not (Hashtbl.mem env el) then failwith ("Undeclared element: " ^ el)
  ) defn.elements;
  
  (* Check faces if present *)
  (match defn.faces with
   | Some faces ->
       List.iter (fun f ->
         if not (Hashtbl.mem env f) then failwith ("Undeclared face: " ^ f)
       ) faces
   | None -> ());
  
  (* Check constraints *)
  List.iter (fun c ->
    match c with
    | Eq (t1, t2) ->
        let rec check_term t =
          match t with
          | Id id -> if not (Hashtbl.mem env id) then failwith ("Undeclared term: " ^ id)
          | Comp (t1, t2) -> check_term t1; check_term t2
          | Inv t -> check_term t
          | Pow (t, _) -> check_term t
          | E -> ()
        in
        check_term t1; check_term t2
    | Map (id1, ids2) ->
        if not (Hashtbl.mem env id1) then
          failwith ("Undeclared map source: " ^ id1);
        List.iter (fun id2 ->
          if not (Hashtbl.mem env id2) then
            failwith ("Undeclared map target: " ^ id2)
        ) ids2
  ) defn.constraints;
  
  (* Type-specific rank check *)
  (match defn.typ, defn.rank with
   | Simplex, Finite n ->
       if List.length defn.elements <> n + 1 then
         failwith "Simplex rank mismatch (elements)";
       (match defn.faces with
        | Some faces ->
            if List.length faces <> n + 1 then
              failwith "Simplex rank mismatch (faces)"
        | None -> failwith "Simplex requires faces")
   | Simplex, Infinite ->
       failwith "Simplex cannot have infinite rank (use Simplicial)"
   | Group, Finite n | Monoid, Finite n ->
       if List.length defn.elements <> n then
         failwith "Group/Monoid rank mismatch (n = generator count)"
   | Group, Infinite | Monoid, Infinite ->
       failwith "Group/Monoid cannot have infinite rank"
   | Simplicial, Finite n | Chain, Finite n | Category, Finite n ->
       if n < 0 then
         failwith "Simplicial/Chain/Category rank must be non-negative"
   | Simplicial, Infinite | Chain, Infinite | Category, Infinite ->
       ()
  );
  
  (* Success *)
  Printf.printf "Type %s checked successfully\n" defn.name

(* Example definitions *)
let singular_cone = {
  name = "singular_cone";
  typ = Simplex;
  context = [
    Decl (["p"; "q"; "r"; "s"], Simplex);
    Decl (["qrs"; "prs"; "pqs"], Simplex);
    Equality ("pqr", Comp (Id "pqs", Id "qrs"), Id "pqr")
  ];
  rank = Finite 3;
  elements = ["p"; "q"; "r"; "s"];
  faces = Some ["qrs"; "prs"; "pqs"; "pqr"];
  constraints = [Eq (Id "pqr", Comp (Id "pqs", Id "qrs"))]
}

let mobius = {
  name = "Möbius";
  typ = Simplex;
  context = [
    Decl (["a"; "b"; "c"], Simplex);
    Decl (["bc"; "ac"], Simplex);
    Equality ("ab", Comp (Id "bc", Id "ac"), Id "ab")
  ];
  rank = Finite 2;
  elements = ["a"; "b"; "c"];
  faces = Some ["bc"; "ac"; "ab"];
  constraints = [Eq (Id "ab", Comp (Id "bc", Id "ac"))]
}

let degen_tetra = {
  name = "degen_tetra";
  typ = Simplex;
  context = [
    Decl (["p"; "q"; "r"; "s"], Simplex);
    Equality ("q", Id "r", Id "q");
    Decl (["qrs"; "prs"; "pqs"], Simplex);
    Equality ("pqr", Comp (Id "pqs", Id "qrs"), Id "pqr")
  ];
  rank = Finite 3;
  elements = ["p"; "q"; "r"; "s"];
  faces = Some ["qrs"; "prs"; "pqs"; "pqr"];
  constraints = [Eq (Id "pqr", Comp (Id "pqs", Id "qrs"))]
}

let twisted_annulus_1 = {
  name = "twisted_annulus_1";
  typ = Simplex;
  context = [
    Decl (["a"; "b"; "c"; "d"], Simplex);
    Decl (["bc"; "ac"; "bd"], Simplex);
    Equality ("ab", Comp (Id "bc", Id "ac"), Id "ab");
    Equality ("cd", Comp (Id "ac", Id "bd"), Id "cd")
  ];
  rank = Finite 2;
  elements = ["a"; "b"; "c"];
  faces = Some ["bc"; "ac"; "ab"];
  constraints = [Eq (Id "ab", Comp (Id "bc", Id "ac"))]
}

let twisted_annulus_2 = {
  name = "twisted_annulus_2";
  typ = Simplex;
  context = [
    Decl (["a"; "b"; "c"; "d"], Simplex);
    Decl (["bc"; "ac"; "bd"], Simplex);
    Equality ("ab", Comp (Id "bc", Id "ac"), Id "ab");
    Equality ("cd", Comp (Id "ac", Id "bd"), Id "cd")
  ];
  rank = Finite 2;
  elements = ["b"; "c"; "d"];
  faces = Some ["bc"; "bd"; "cd"];
  constraints = [Eq (Id "cd", Comp (Id "ac", Id "bd"))]
}

let degen_triangle = {
  name = "degen_triangle";
  typ = Simplex;
  context = [
    Decl (["a"; "b"; "c"], Simplex);
    Equality ("b", Id "c", Id "b");
    Decl (["bc"; "ac"], Simplex);
    Equality ("ab", Comp (Id "bc", Id "ac"), Id "ab")
  ];
  rank = Finite 2;
  elements = ["a"; "b"; "c"];
  faces = Some ["bc"; "ac"; "ab"];
  constraints = [Eq (Id "ab", Comp (Id "bc", Id "ac"))]
}

let singular_prism = {
  name = "singular_prism";
  typ = Simplex;
  context = [
    Decl (["p"; "q"; "r"; "s"; "t"], Simplex);
    Decl (["qrs"; "prs"; "pqt"], Simplex);
    Equality ("qrs", Id "qrs", Id "qrs");
    Equality ("pqr", Comp (Id "pqt", Id "qrs"), Id "pqr")
  ];
  rank = Finite 3;
  elements = ["p"; "q"; "r"; "s"];
  faces = Some ["qrs"; "prs"; "pqt"; "pqr"];
  constraints = [Eq (Id "pqr", Comp (Id "pqt", Id "qrs"))]
}

let path_z2_category = {
  name = "path_z2_category";
  typ = Category;
  context = [
    Decl (["x"; "y"], Simplex);
    Decl (["f"; "g"; "h"], Simplex);
    Decl (["e"; "a"], Simplex);
    Equality ("a2", Pow (Id "a", S2), Id "e");
    Equality ("h", Comp (Id "f", Id "g"), Id "h")
  ];
  rank = Finite 2;  (* 2 objects: x, y *)
  elements = ["x"; "y"];
  faces = None;  (* No faces for Category *)
  constraints = [Eq (Id "h", Comp (Id "f", Id "g"))]
}

let nat_monoid = {
  name = "nat_monoid";
  typ = Monoid;
  context = [
    Decl (["z"; "s"], Simplex);
    Equality ("sz", Comp (Id "s", Id "z"), Id "s");
    Equality ("zs", Comp (Id "z", Id "s"), Id "s")
  ];
  rank = Finite 2;  (* 2 generators: z, s *)
  elements = ["z"; "s"];
  faces = None;  (* No faces for Monoid *)
  constraints = [
    Eq (Id "sz", Comp (Id "s", Id "z"));
    Eq (Id "zs", Comp (Id "z", Id "s"))
  ]
}

let triangle_chain = {
  name = "triangle_chain";
  typ = Chain;
  context = [
    Decl (["v0"; "v1"; "v2"; "e01"; "e02"; "e12"; "t"], Simplex);
    Equality ("∂₁₀", Id "e01", Id "∂₁₀");
    Equality ("∂₁₁", Id "e02", Id "∂₁₁");
    Equality ("∂₁₂", Id "e12", Id "∂₁₂");
    Equality ("∂₂", Id "t", Id "∂₂")
  ];
  rank = Finite 2;  (* Chain length: 0 -> 1 -> 2 *)
  elements = ["v0"; "v1"; "v2"; "e01"; "e02"; "e12"; "t"];
  faces = None;  (* No faces for Chain *)
  constraints = [
    Eq (Id "∂₁₀", Id "e01");
    Eq (Id "∂₁₁", Id "e02");
    Eq (Id "∂₁₂", Id "e12");
    Map ("∂₂", ["e01"; "e02"; "e12"])
  ]
}

let circle = {
  name = "circle";
  typ = Simplicial;
  context = [
    Decl (["v"; "e"], Simplex);
    Equality ("∂₁₀", Id "v", Id "∂₁₀");
    Equality ("∂₁₁", Id "v", Id "∂₁₁");
    Equality ("s₀", Id "e", Id "s₀")
  ];
  rank = Finite 1;  (* Max dimension: 1 *)
  elements = ["v"; "e"];
  faces = None;  (* No faces for Simplicial *)
  constraints = [
    Eq (Id "∂₁₀", Id "v");
    Eq (Id "∂₁₁", Id "v");
    Map ("s₀", ["v"])
  ]
}

let z3 = {
  name = "z3";
  typ = Group;
  context = [
    Decl (["e"; "a"], Simplex);
    Equality ("a3", Pow (Id "a", S3), Id "e")
  ];
  rank = Finite 1;  (* 1 generator: a *)
  elements = ["a"];
  faces = None;  (* No faces for Group *)
  constraints = [Eq (Id "a3", Pow (Id "a", S3))]
}

let s1_infty = {
  name = "s1_infty";
  typ = Simplicial;
  context = [
    Decl (["v"; "e"], Simplex);
    Equality ("∂₁₀", Id "v", Id "∂₁₀");
    Equality ("∂₁₁", Id "v", Id "∂₁₁");
    Equality ("s₀", Id "e", Id "s₀");
    Equality ("∂₂₀", Comp (Id "e", Id "e"), Id "∂₂₀");
    Equality ("s₁₀", Id "∂₂₀", Id "s₁₀")
  ];
  rank = Infinite;  (* Unbounded dimensions *)
  elements = ["v"; "e"; "∂₂₀"];
  faces = None;  (* No faces for Simplicial *)
  constraints = [
    Eq (Id "∂₁₀", Id "v");
    Eq (Id "∂₁₁", Id "v");
    Map ("s₀", ["v"]);
    Eq (Id "∂₂₀", Comp (Id "e", Id "e"));
    Map ("s₁₀", ["∂₂₀"])
  ]
}

let cube_infty = {
  name = "cube_infty";
  typ = Category;
  context = [
    Decl (["a"; "b"; "c"], Simplex);
    Decl (["f"; "g"; "h"], Simplex);
    Equality ("cube2", Comp (Id "g", Id "f"), Id "h");
    Equality ("cube3", Comp (Id "cube2", Id "f"), Id "cube3");
  ];
  rank = Infinite; 
  elements = ["a"; "b"; "c"];
  faces = Some ["cube2"; "cube3"];
  constraints = [
    Eq (Id "cube2", Comp (Id "g", Id "f"));
    Eq (Id "cube3", Comp (Id "cube2", Id "f"))
  ]
}

let examples = [
  singular_cone; mobius; degen_tetra; twisted_annulus_1; twisted_annulus_2;
  degen_triangle; singular_prism; path_z2_category; nat_monoid; triangle_chain;
  circle; z3; s1_infty; cube_infty
]

let () = List.iter check_type_def examples
