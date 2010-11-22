open Batteries
open Printf

module Vint =
struct
  include Int64
(*type t = Int64.t*)

  type parse_ret = Num of t | Reserved of int
      
  let find_range x = 
    let rec finder i = 
      let max = sub (shift_left 1L (8 * i + 7)) 2L in
      if x < max then i else finder (i+1)
    in
    let i = finder 0 in
    (i, 1 lsl (7-i))

  let find_len c0 =
    let table = [|-1; 7; 6; 6; 5; 5; 5; 5; 4; 4; 4; 4; 4; 4; 4; 4;
		   3; 3; 3; 3; 3; 3; 3; 3; 3; 3; 3; 3; 3; 3; 3; 3;
		   2; 2; 2; 2; 2; 2; 2; 2; 2; 2; 2; 2; 2; 2; 2; 2;
		   2; 2; 2; 2; 2; 2; 2; 2; 2; 2; 2; 2; 2; 2; 2; 2;
		   1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1;
		   1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1;
		   1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1;
		   1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1 |]
    and sub_table = [| 0; 0x80; 0x40; 0x20; 0x10; 0x08; 0x04; 0x02; 0x01|] in
    let len = table.(c0) in
    (len, c0 - sub_table.(len))

(*
    if c0 >= 0x80 then (0, c0-0x80)
    else if c0 >= 0x40 then (1, c0 - 0x40)
    else if c0 >= 0x20 then (2, c0 - 0x20)
    else if c0 >= 0x10 then (3, c0 - 0x10)
    else if c0 >= 0x08 then (4, c0 - 0x08)
    else if c0 >= 0x04 then (5, c0 - 0x04)
    else if c0 >= 0x02 then (6, c0 - 0x02)
    else if c0 >= 0x01 then (7, c0 - 0x01)
    else failwith "Initial byte of vint = 0" *)
      
  let to_string ?(max=8) t = 
    let (cnt, bit1) = find_range t in
    if cnt > max then failwith "Exceeded max size allowed in Vint.to_string";
    let ret = String.create (cnt+1) in
    let get_byte x = 0xff land to_int x in
    let rec fill_bytes v pos sm = 
      match pos with
	  0 -> 
	    let msbs = sm land (get_byte v) in
	    ret.[0] <- Char.chr (bit1 lor msbs)
	| _ ->
	    let next_v = shift_right_logical v 8
	    and sm = sm lsr 1 in
	    ret.[pos] <- Char.chr (get_byte v);
	    fill_bytes next_v (Pervasives.pred pos) sm
    in
    fill_bytes t cnt 0xff;
    ret

  open Cf_parser.Op

  let parse_byte = 
    Cf_parser.tok begin function c -> 
      Some (Char.code c) 
    end
	
  let of_seq ?(max=8) =
    parse_byte >>= fun c0 ->
      let (len, out0) = find_len c0 in
      if len > max then 
	failwith "Exceeded max size allowed in Vint.to_of_seq"
      else 
	let is_resv = (out0 = ((1 lsl len) - 1)) in
	let rec proc_char acc rem pr = (* parses the rest *)
	  if rem = 0 then ~: (acc,pr)
	  else 
	    parse_byte >>= fun cn ->
	      let a' = 
		logor 
		  (shift_left acc 8) 
		  (of_int cn) in
	      proc_char a' (Pervasives.pred rem) (pr && (cn = 0xff))
	in
	proc_char (of_int out0) len is_resv >>= fun (v,resv) ->
	  if resv 
	  then ~: (Reserved len)
	  else ~: (Num v)
	  

let of_seq_head ?(max=8) s = 
match of_seq ~max s with 
Some (Num v, _) -> v 
| Some (Reserved _, _) -> failwith "found reserved vint; expected proper number"
| None -> failwith "error parsing vint"

  let to_seq ?(max=8) t = Cf_seq.of_string (to_string ~max t)
  let of_string ?(max=8) str = of_seq ~max (Cf_seq.of_string str)

  let to_hex_string i =
    let enc = to_string i in
    Cryptokit.transform_string (Cryptokit.Hexa.encode ()) enc

  let test () = 
    let print_pair c i =
      Printf.printf "c:%d int %15Lx -> %15s\n" c i (to_hex_string i)
    in

    let print_pair_eid c i =
      Printf.printf "c:%d int %15Lx -> %15s EID\n" c i (to_hex_string i)
    in

    for i = 1 to 27 do
      let i_n = (shift_left one i) in
      let i_n1 = pred i_n in
      print_pair i i_n;
      print_pair i i_n1;
      print_pair_eid i i_n;
      print_pair_eid i i_n1;
    done;

(*    for i = 27 to 55 do
      let i_n = (shift_left one i) in
      let i_n1 = pred i_n in
      print_pair i i_n;
      print_pair i i_n1;
    done;
 *)
    let rand = Crypto.MT19937.self_init () in
    for i = 1 to 3 do
      let (a, b) = ((Crypto.MT19937.random_int32 rand), (Crypto.MT19937.random_int32 rand)) in
      let (a', b') = (of_int32 a, of_int32 b) in
      let r = logor (shift_left a' 23) b' in
      print_pair i r
    done

end;;

module Eb_types = 
struct

  type eb_value_type = 
      [ `Int_t 
      | `Uint_t 
      | `Float_t 
      | `String_t 
      | `Date_t 
      | `Binary_t ]

  module Eb_int = Vint
  module Eb_uint = Vint
  module Eb_float = struct
    type t = 
	F0 
      | F4 of float 
      | F8 of float 
      | F10 of float (* only has 8 bytes of precision *)
    let to_string = function
	F0 -> ""
      | F4 v -> Crypto.string_of_i32 (Int32.bits_of_float v)
      | F8 v -> Crypto.string_of_i64 (Int64.bits_of_float v)
      | F10 v -> "\000\000" ^ Crypto.string_of_i64 (Int64.bits_of_float v)
    let of_seq seq = 
      match Cf_seq.length seq with
	0 -> F0 
      | 4 -> F4 (Int32.float_of_bits (Crypto.i32_of_seq seq))
      | 8 -> F8 (Int64.float_of_bits (Crypto.i64_of_seq seq))
      | 10 -> F10 (Int64.float_of_bits (Crypto.i64_of_seq (Cf_seq.shift 2 seq)))
      | l -> failwith "Cannot convert %i bytes into a float" l
  end
  module Eb_string = struct
    type t = string (* unicode (UTF-8) string *)
  end
  module Eb_date = struct
    include Int64 (* nanoseconds to the millennium *)
	
(* constants for date conversions *)
    let mult = of_string "1000000000"
    and skew = of_int 978307200 (*2001/01/01 00:00:00 UTC*)
    let date_of_unix_date ud = 
      mul (sub (of_int ud) skew) mult
    let unix_date_of_date d =
      to_int (add (div d mult) skew)
  end
  module Eb_binary = struct
    type t = string (* octet sequence - one byte per character *)
  end

  (* parser types *)
	  
  type eb_val = [
      `Int_v of Eb_int.t
    | `Uint_v of Eb_uint.t
    | `Float_v of Eb_float.t
    | `String_v of Eb_string.t
    | `Date_v of Eb_date.t
    | `Binary_v of Eb_binary.t
  ]

  type 'a value = eb_val constraint 'a = eb_value_type

  type eb_type = [ eb_value_type | `Container_t ]

  type eb_id = Vint.t

  let date_of_str s = Vint.of_int 10
	  
  type name = string

  let eb_val_to_str = function
      `Int_v v -> Eb_int.to_string v
    | `Uint_v v -> Eb_uint.to_string v
    | `Float_v v -> Eb_float.to_string v
    | `String_v s -> s
    | `Ustring_v us -> us
    | `Date_v d -> Crypto.string_of_i64 d
    | `Binary_v b -> b

  let eb_val_of_seq seq = function
      `Int_t -> `Int_v (Vint.of_seq_head seq)
    | `Uint_t -> `Uint_v (Vint.of_seq_head seq)
    | `Float_t -> `Float_v (Eb_float.of_seq seq)
    | `String_t -> `String_v (Cf_seq.to_string seq)
    | `Date_t -> `Date_v (Crypto.i64_of_seq seq)
    | `Binary_t -> `Binary_v (Cf_seq.to_string seq)

  let val_of_int x = `Int_v (Vint.of_int x)
  let val_of_int64 x = `Int_v x
  let val_of_uint x = `Uint_v (Vint.of_int x)
  let val_of_uint64 x = `Uint_v x
  let val_of_float x = `Float_v x
  let val_of_string x = `String_v x
  let val_of_date x = `Date_v (Vint.of_int x)
  let val_of_date64 x = `Date_v x
  let val_of_binary x = `Binary_v x

end

module Eb_dtd =
  struct
    
    open Eb_types

    module Eb_card : 
	sig
	  type t = Zero_plus | Zero_one | One | One_plus
	  val default : t
	  val of_char : char -> t
	  val to_char : t -> char
	  val allow_zero : t -> bool
	  val allow_more : t -> bool
	end = struct
	  type t = Zero_plus | Zero_one | One | One_plus
	  let default = Zero_one
	  let of_char = function 
	    | '*' -> Zero_plus 
	    | '?' -> Zero_one 
	    | '1' -> One 
	    | '+' -> One_plus
	    | _ -> invalid_arg "Not a cardinal_type character"
	  let to_char = function
	    | Zero_plus -> '*'
	    | Zero_one -> '?'
	    | One -> '1'
	    | One_plus -> '+'
	  let allow_zero = function
	      Zero_plus -> true
	    | Zero_one -> true
	    | One -> false
	    | One_plus -> false
	  let allow_more = function
	    | Zero_plus -> true
	    | Zero_one -> false
	    | One -> false
	    | One_plus -> true
	end

    module Eb_test :
	sig
	  type 'a t = 'a -> bool

	  val andt : 'a t -> 'a t -> 'a t
	  val flatten : 'a t list -> 'a t
	      
	  val null : 'a t
	  val test_false : 'a t
	  val rng_unit : 'a -> 'a t
	  val rng_lthan : 'a -> 'a t
	  val rng_leq : 'a -> 'a t
	  val rng_gthan : 'a -> 'a t
	  val rng_geq : 'a -> 'a t
	  val rng_betw : 'a -> 'a -> 'a t
	  val rng_betw_inc_left : 'a -> 'a -> 'a t
	  val rng_betw_inc_rght : 'a -> 'a -> 'a t
	  val rng_betw_inc_both : 'a -> 'a -> 'a t
	  val rng_string : Eb_uint.t t -> eb_val t
	end = struct
	  
	  type 'a t = 'a -> bool
	      
	  let andt f_new f_old = fun x -> f_new x && f_old x
	      
	  let flatten rng = fun x -> 
	    let rec check_each = function
	      | [] -> true
	      | h :: t when h x -> check_each t
	      | _ -> false
	    in 
	    check_each rng
	      
	      (* converts a uint test into a string test *)
	  let rng_string rng sv =
	    match sv with 
	    | `String str ->
		let len = String.length str in
		let rec check_pos p =
		  if p < 0 then true 
		  else if rng (Vint.of_int (Char.code str.[p]))
		  then check_pos (pred p)
		  else false
		in
		check_pos len
	    | #eb_val -> false
	  let null = fun _ -> true
	  let test_false = fun _ -> false
	  let rng_unit u = function x -> x = u
	  let rng_lthan u = function x -> x < u
	  let rng_leq u = function x -> x <= u
	  let rng_gthan u = function x -> x > u
	  let rng_geq u = function x -> x >= u
	  let rng_betw u v = function x -> u < x && x < v
	  let rng_betw_inc_left u v = function x -> u <= x && x < v
	  let rng_betw_inc_rght u v = function x -> u < x && x <= v
	  let rng_betw_inc_both u v = function x -> u <= x && x <= v
	      
	end (* eb_test *)

    module Eb_params =
      struct
	
	type typ_props = {
	    prop_type : 'a;
	    default   : 'a value option;
	    range     : 'a value Eb_test.t; 
	  }
	constraint 'a = eb_value_type
	      
	type con_props = {
	    children : bool;
	    ordered  : bool;
	  }

	type typ_props_u = [ 
	    `Val_p of typ_props
	  | `Container_p of con_props
	  ]

	let props_type_inner : typ_props_u -> eb_type = function
	    `Val_p r -> ( r.prop_type : eb_value_type :> eb_type )
	  | `Container_p _ -> `Container_t
		
	type parlev = 
	  | Root
	  | Par of name list 
	  | Level of int Eb_test.t (* not unbounded on left *) 

	type t = { (* make private in signature *)
	    pl      : parlev;
	    card    : Eb_card.t;
	    size    : Eb_uint.t Eb_test.t; (* un-merged list *)
	    typed   : typ_props_u;
	  }
	      
	let props_type : t -> eb_type = fun p -> props_type_inner p.typed
	    
	let default_typed = function
	    #eb_value_type as t ->
	      `Val_p {prop_type = t; default = None; range = Eb_test.null}
	  | `Container_t -> `Container_p {children = false; ordered = true;}
		
	let default_props t prnt = 
	  let pl = match prnt with None -> Root | Some p -> Par [p] in
	  { pl = pl;
	    card = Eb_card.default;
	    size = Eb_test.null;
	    typed = default_typed t;
	  }
	    
	let add_par par p = 
	  match p.pl with
	    Root -> {p with pl = Par [par]}
	  | Par pl -> {p with pl = Par (par :: pl)}
	  | Level _ -> failwith "Cannot add parent to an element with a level"
	    
	let add_parl pl p =
	  match p.pl with
	    Root -> {p with pl = Par pl}
	  | Par pl' -> {p with pl = Par (List.rev_append pl pl')}
	  | Level _ -> failwith "Cannot add parent to an element with a level"
	    
	let add_lev l p =
	  match p.pl with
	    Root -> {p with pl = Level l}
	  | Par _ -> failwith "Cannot add a level to an element with parents"
	  | Level l' -> {p with pl = Level l}
	    
	let add_card c p = {p with card = c}
	let add_size s p = {p with size = Eb_test.andt s p.size }
	    
	let set_ord_inner o' typed = 
	  match typed with
	    `Container_p c -> `Container_p {c with ordered = o'}
	  | _ -> failwith "Cannot set_ord a non-container"
		
	let set_children_inner c' typed =
	  match typed with
	    `Container_p c -> `Container_p {c with children = c'}
	  | _ -> failwith "Cannot set_children a non-container"
		
	let add_def_inner d = function
	    `Val_p t -> `Val_p {t with default = Some d}
	  | `Container_p _ -> failwith "Cannot default a container"

	let add_rng_inner r = function
	    `Val_p t -> `Val_p {t with range = Eb_test.andt r t.range}
	  | `Container_p _ -> failwith "Cannot range a container"

	let box_mod typ untyped_modification = function
	    `Val_p r when r.prop_type = typ -> `Val_p (untyped_modification r)
	  | _ ->  failwith "Incompatible types in mod-boxer"
		
	let lift_typed typ_mod = fun p ->
	  {p with typed = typ_mod p.typed}
	    
	let set_ord o p = lift_typed (set_ord_inner o) p
	let set_children c p = lift_typed (set_children_inner c) p
	let add_def d p = lift_typed (add_def_inner d) p
	let add_rng r p = lift_typed (add_rng_inner r) p

	let get_def p = 
	  match p.typed with 
	  | `Val_p r -> r.default
	  | `Container_p _ -> None	       
      end

    open Eb_params

    module Ctx = struct
      let root_ctx_id = Vint.minus_one

      type ctx_rec = { 
	  id : eb_id;
	  zero: bool;
	  more: bool;
	  default: eb_val option;
	}
      type t = ctx_rec Cf_deque.t

      let rec_of_props id props = {
	id = id;
	zero = Eb_card.allow_zero props.card;
	more = Eb_card.allow_more props.card;
	default = get_def props;
      }
	
      let add_rec r t = Cf_deque.A.push r t

      let add_props id props t = add_rec (rec_of_props id props) t

      let ok ctx id pl lev = 
	try 
	  match pl with
	    Root -> lev = 1
	  | Par pl -> (Cf_deque.B.head ctx).id = id
	  | Level ltest -> ltest lev
	with 
	  Not_found -> false
      and zero ctx = (Cf_deque.B.head ctx).zero
      and more ctx = (Cf_deque.B.head ctx).more
      and hd ctx = Cf_deque.B.head ctx
      and tl ctx = Cf_deque.B.tail ctx 
	  
      let next ctx id = 
	match Cf_deque.B.pop ctx with
	| Some (r, _) when r.id != id ->
	    ctx
	| Some (r,tl) when r.more ->
	    Cf_deque.B.push {r with zero=true; default=None} tl
	| Some (r,tl) -> 
	    tl
	| None -> 
	    Cf_deque.nil
	      
      let make_default make_rec ctx acc = 
	match Cf_deque.B.pop ctx with
	  None -> (acc, ctx)
	| Some (r,tl) ->
	    match r.default with
	      Some v -> ((make_rec r.id v):: acc, tl)
	    | None -> (acc, tl)

      let expectid ctx = (hd ctx).id
    end

(* full DTD type specification *)

    module NameMap = Cf_rbtree.Map(struct 
      type t=name 
      let compare = Pervasives.compare 
    end)
    module IdMap = Cf_rbtree.Map(Vint)
	
    type dtd = {
	header   : eb_val NameMap.t;             (* header name -> eb_val *)
	ids      : eb_id NameMap.t;              (* name -> id *)
	elements : (name * Eb_params.t) IdMap.t; (* id -> name, params *)
	ctx      : Ctx.t IdMap.t;                (* parent id -> context *)
	types    : Eb_params.typ_props_u NameMap.t; (* typename -> typ_props *)
      }
	  
    let (==>) x f = f x
    let apply_pp fl x = List.fold_left (==>) x (List.rev fl)
	
(* simplified types for conversion into proper dtd *)

    let id_of_name dtd n = 
      let n = String.lowercase n in
      NameMap.search n dtd.ids

    let insert_tag n id props = fun dtd ->
      let n = String.lowercase n in
      let (ids', coll) = NameMap.insert (n, id) dtd.ids in
      if coll <> None then failwith (Printf.sprintf "Name %s already used\n" n);
      let (ele', coll) = IdMap.insert (id, (n, props)) dtd.elements in
      if coll <> None then failwith (Printf.sprintf "ID %LX already used\n" id);
      let ctx' = 
	let add_context acc pid = 
	  IdMap.modify pid (Ctx.add_props id props) acc in
	match props.pl with
	  Root -> add_context dtd.ctx Ctx.root_ctx_id
	| Par pl -> 
	    pl 
	      ==> List.rev_map (id_of_name dtd)
	      ==> List.fold_left add_context dtd.ctx
	| Level l -> dtd.ctx
      in
      { dtd with ids = ids'; elements = ele'; ctx = ctx' }

    let modify_tag id modfun = fun dtd ->
      let modfun' (n, tag) = (n, modfun tag) in
      let ele' = IdMap.modify id modfun' dtd.elements in
      { dtd with elements = ele' }

    let modify_tag_by_name n modfun = fun dtd -> 
      let id = id_of_name dtd n in
      modify_tag id modfun dtd

    let add_parent_retro n newpar = fun dtd ->      
      let id = id_of_name dtd n in
      let props = ref (Obj.magic 0) in (* set by modprop *)
      let ele' = 
	let modprop (n,prop) = 
	  props := prop; (* save a copy of prop for later *)
	  (n, add_par newpar prop)
	in
	IdMap.modify id modprop dtd.elements
      and ctx' = 
	let pid = id_of_name dtd newpar in
	IdMap.modify pid (Ctx.add_props id !props) dtd.ctx in
      { dtd with elements = ele'; ctx = ctx' }



    let new_dtd = {
      header = NameMap.nil;
      ids = NameMap.nil;
      elements = IdMap.nil;
      ctx = IdMap.nil;
      types = NameMap.nil;
    }
	
    let ebml_id = Vint.of_int 0x1a45dfa3 (* safe because 1a < 7f for first byte *)
    let ebml_version_id = Vint.of_int 0x4286
    let ebml_read_version_id = Vint.of_int 0x42f7
    let ebml_max_id_len_id = Vint.of_int 0x42f2
    let ebml_max_size_len_id = Vint.of_int 0x42f3
    let doctype_id = Vint.of_int 0x4282
    let doctype_version_id = Vint.of_int 0x4287
    let doctype_read_version_id = Vint.of_int 0x4285
	
    let default_dtd_pre_ = 
      "define elements {
	 EBML := 1a45dfa3 container [ card:+; ] {
	   EBMLVersion := 4286 uint [ def:1; ]
	   EBMLReadVersion := 42f7 uint [ def:1; ]
	   EBMLMaxIDLength := 42f2 uint [ def:4; ]
	   EBMLMaxSizeLength := 42f3 uint [ def:8; ]
	   DocType := 4282 string [ range:32..126; ]
	   DocTypeVersion := 4287 uint [ def:1; ]
	   DocTypeReadVersion := 4285 uint [ def:1; ]
	 }

 	 CRC32 := c3 container [ level:1..; card:*; ] {
	   %children;
	   CRC32Value := 42fe binary [ size:4; ]
	 }
	 Void  := ec binary [ level:1..; card:*; ]
       }"


    open Cf_parser.X
    open Cf_parser.Op
    open Cf_lexer.Op
    let ( >>=! ) m f s = match m s with None -> None | Some ((), s) -> f s
    let err_expect s = Cf_parser.err (fun _ -> failwith ("Expected " ^ s))
	
    type 'a p_type = (Cf_lexer.line_cursor, char, 'a) Cf_parser.X.t
    type top_p_type = (dtd -> dtd) p_type

    let wsp_ = !^(function ' ' | '\009' | '\010' | '\013' -> true | _ -> false)
    let wsp = Cf_lexer.create (wsp_ $= ())
	
    let is_cr_or_lf_ x = !^(function '\010' | '\013' -> x | _ -> not x)
    let lcomment_ = 
      !:'\\' $& !:'\\' $& 
      (!* (is_cr_or_lf_ false)) $& (is_cr_or_lf_ true)
	
    let no_star_ = !^(function '*' -> false | _ -> true)
    let no_slash_ = !^(function '/' -> false | _ -> true)
    let bcomment_ = (* correct but ugly *)
      !$"/*" $& 
      (!*(!* no_star_ $& (!+ (!:'*')) $& no_slash_)) $& (* can have stars in the middle, just without a slash *)
      (!* no_star_) $& !$"*/"
    let comment_ = lcomment_ $| bcomment_
    let s_lr = ((!*wsp_) $| ((!*wsp_) $& comment_ $& (!*wsp_))) $= ()
    let spc = Cf_lexer.create s_lr


    let alpha_under_ = !^(function 'a'..'z' | 'A'..'Z' | '_' -> true | _ -> false)
    let alpha_under_num_ = !^(function 'a'..'z' | 'A'..'Z' | '_' | '0'..'9' -> true | _ -> false)
    let name_lr = (alpha_under_ $& (!+ alpha_under_num_)) $^ (fun x -> x)
    let get_name = Cf_lexer.create name_lr
	
    let hexdig_ = !^(function 'a'..'f' | 'A'..'F' | '0'..'9' -> true | _ -> false)
    let two_hex_ = hexdig_ $& hexdig_
    let id_lr = (!+ two_hex_) $^ (fun x -> Hexutil.int64_of_hex x)
    let get_id = Cf_lexer.create id_lr

    let get_type : eb_value_type p_type = 
      Cf_parser.alt [lit "int" `Int_t;
		     lit "uint" `Uint_t;
		     lit "float" `Float_t;
		     lit "string" `String_t;
		     lit "date" `Date_t;
		     lit "binary" `Binary_t;
		     err_expect "a datatype";
		   ]


    let card_token_ = !^(function '*' | '?' | '1' | '+' -> true | _ -> false)
    let card_token_lr = (card_token_ $^ (fun s -> Eb_card.of_char s.[0]))
    let get_card = Cf_lexer.create card_token_lr

    let digit_ = !^(function '0'..'9' -> true | _ -> false)
    let int_v_ = (!?(!:'-')) $& (!+digit_)
    let int_v_lr = int_v_ $^ (fun s -> `Int_v (Int64.of_string s))
    let get_int = Cf_lexer.create int_v_lr

    let uint_v_lr = !+digit_ $^ (fun s -> `Uint_v (Int64.of_string s))
    let get_uint = Cf_lexer.create uint_v_lr

    let uint_v_lr_ut = !+digit_ $^ Int64.of_string
    let get_uint_untagged = Cf_lexer.create uint_v_lr_ut

    let uint_v_lr_31 = !+digit_ $^ int_of_string
    let get_uint_31 = Cf_lexer.create uint_v_lr_31

    let float_v_ = int_v_ $& !:'.' $& (!+digit_) $& (!?(!:'e' $& (!?((!:'+' $| !:'-') $& (!+digit_)))))
    let float_v_lr = float_v_ $^ (fun s -> `Float_v (Eb_float.F8 (float_of_string s)))
    let get_float = Cf_lexer.create float_v_lr

    let two_digit_ = digit_ $& digit_
    let date_v_ = (!?digit_) $& two_digit_ $& two_digit_ $&
      (!? (!:'\054' $& two_digit_ $& !:':' $& two_digit_ $& 
	   !:':' $& two_digit_ $& (!? (!:'.' $& (!*digit_)))))
    let date_v_lr = date_v_ $^ (fun s -> `Date_v (date_of_str s))
    let get_date = Cf_lexer.create date_v_lr

    let str_bin_ = !$"0x" $& (!+two_hex_)
    let flatten_str s = 
      assert (s.[0] = '0');
      assert (s.[1] = 'x');
      Hexutil.string_of_hex s
    let str_bin_lr = str_bin_ $^ (fun s -> `String_v (flatten_str s))
    let strcha_ = !^(function '\020' | '\021' | '\023'..'\126' -> true | _ -> false)
    let str_quo_ = !:'\022' $& (!*strcha_) $& !:'\022'
    let trim_quotes s = String.sub s 1 (String.length s - 2)
    let str_quo_lr = str_quo_ $^ (fun s -> `String_v (trim_quotes s))
    let get_string = Cf_lexer.create (!@ [str_bin_lr; str_quo_lr])

    let get_binary = get_string

    let get_val_any = Cf_parser.alt 
	[get_int; get_float; get_date; get_string]
	 (* binary? uint? *)

    let get_val_typ : (eb_value_type as 'a) -> (char * Cf_lexer.line_cursor, 'a value) Cf_parser.t = function
	`Int_t -> get_int
      | `Uint_t -> get_uint
      | `Float_t -> get_float
      | `Date_t -> get_date
      | `String_t -> get_string
      | `Binary_t -> get_binary

    let get_list sat_sep get_item = 
      let sep_get = sat_sep >>= fun _ -> get_item in
      get_item >>= fun hd -> 
	(?* sep_get) >>= fun tl -> 
	  ~: (hd::tl)

    let sat_dotdot_ = lit ".." ()
    let p_dotdot_rng gv =
      (?/ gv) >>= function
	| None -> (* .. val *)
	    (sat_dotdot_ >>=! gv >>= fun v2 -> 
	      ~: (Eb_test.rng_leq v2))
	| Some v1 -> 
	    (?/ sat_dotdot_) >>= function
	      | None -> (* val *)
		  ~: (Eb_test.rng_unit v1)
	      | Some _ -> 
		  (?/ gv) >>= function
		    | None -> (* val .. *)
			~: (Eb_test.rng_geq v1)
		    | Some v2 -> (* val .. val *)
			~: (Eb_test.rng_betw_inc_both v1 v2)
    let p_dotdot_urng gv = (* doesn't allow ..val *)
      gv >>= fun v1 ->
	(?/ sat_dotdot_) >>= function
	  | None -> (* val *)
	      ~: (Eb_test.rng_unit v1)
	  | Some _ -> 
	      (?/ gv) >>= function
		| None -> (* val .. *)
		    ~: (Eb_test.rng_geq v1)
		| Some v2 -> (* val .. val *)
		    ~: (Eb_test.rng_betw_inc_both v1 v2)

    type eb_lcomp = [`Leq | `Lthan ]
    type eb_fcomp = [ eb_lcomp | `Geq | `Gthan ]

    let leq = lit "<=" `Leq
    let lthan = lit "<" `Lthan
    let geq = lit ">=" `Geq
    let gthan = lit ">" `Gthan
    let get_comp : eb_fcomp p_type = Cf_parser.alt [
      leq; lthan; geq; gthan; err_expect "comparison operator";
    ]
    let get_lcomp : eb_lcomp p_type = Cf_parser.alt [
      leq; lthan; err_expect "leq or lthan";
    ]

    let p_float_rng (*: eb_float Eb_test.t p_type*) =
      (?/ get_float) >>= function
	  None ->  (* ex. >= 15.2 *)
	    (get_comp >>= fun comp ->
	      get_float >>= fun v -> 
		match comp with
		| `Leq -> ~: (Eb_test.rng_leq v)
		| `Lthan -> ~: (Eb_test.rng_lthan v)
		| `Geq -> ~: (Eb_test.rng_geq v)
		| `Gthan -> ~: (Eb_test.rng_gthan v))
	| Some v1 -> (* ex 15.1 <= .. <= 15.2 *)
	    get_lcomp >>= fun lcomp1 ->
	      sat_dotdot_ >>=! get_lcomp >>= fun lcomp2 ->
		get_float >>= fun v2 ->
		  match (lcomp1, lcomp2) with
		  | (`Leq, `Leq) -> ~: (Eb_test.rng_betw_inc_both v1 v2)
		  | (`Leq, `Lthan) -> ~: (Eb_test.rng_betw_inc_left v1 v2)
		  | (`Lthan, `Leq) -> ~: (Eb_test.rng_betw_inc_rght v1 v2)
		  | (`Lthan, `Lthan) -> ~: (Eb_test.rng_betw v1 v2)

    let get_rng_uint_ut = p_dotdot_urng get_uint_untagged 
    let get_rng_uint_31 = p_dotdot_urng get_uint_31

    let get_range : (eb_value_type as 'a) -> (char * Cf_lexer.line_cursor, 'a value Eb_test.t) Cf_parser.t = function
	`Int_t -> p_dotdot_rng get_int
      | `Uint_t -> p_dotdot_urng get_uint
      | `Float_t -> p_float_rng
      | `Date_t -> p_dotdot_urng get_date
      | `String_t -> get_rng_uint_ut >>= fun r -> ~: (Eb_test.rng_string r)
      | `Binary_t -> get_rng_uint_ut >>= fun r -> ~: (Eb_test.rng_string r)

    let sat_comma_ = spc >>=! lit "," () >>=! spc
    let get_range_list get_rng = get_list sat_comma_ get_rng

    let type_attr_begin_ name = lit name () >>=! spc >>=! lit ":" () >>=! spc
    let type_attr_end = spc >>=! lit ";" ()

    let p_param pname getter user =
      (type_attr_begin_ pname) >>=! getter >>= fun v -> ~: (user v)

    let p_parent = p_param "parent" (get_list sat_comma_ get_name) add_parl
    let p_level = p_param "level" get_rng_uint_31 add_lev
    let p_card = p_param "card" get_card add_card
	
    let yes_lr = ((!:'1') $| (!$"yes")) $= true
    let no_lr = ((!:'0') $| (!$"no")) $= false
    let get_yesno = Cf_lexer.create (!@ [yes_lr; no_lr])
	
    let p_ord = p_param "ordered" get_yesno set_ord_inner
    let p_size = p_param "size" get_rng_uint_ut add_size
    let p_def t = p_param "def" (get_val_typ t) add_def_inner
    let p_range t = p_param "range" (get_range t) add_rng_inner
	
    let sat_lbrack_ = lit "[" () >>=! spc
    let sat_rbrack_ = spc >>=! lit "]" ()
    let prop_container getter = 
      sat_lbrack_ >>=! (?* getter) >>= fun props ->
	sat_rbrack_ >>=! ~: props
    let get_cprop = Cf_parser.alt [p_parent; p_level; p_card; p_size]

	
    let get_tprop t = 
      Cf_parser.alt [p_def t; p_range t]

    let get_prop t = 
      let lift_presult p = ~: (fun x -> lift_typed p x) in
      Cf_parser.alt 
	[ get_tprop t >>= lift_presult; get_cprop ]
    let get_props t = prop_container (get_prop t)
    let get_cprops = prop_container get_cprop
    let get_tprops t = prop_container (get_tprop t)

    let sat_semi_ = spc >>=! lit ";" ()
    let p_velement : name option -> top_p_type = fun prnt ->
      get_name >>= fun n ->
	get_id >>= fun id -> 
	  get_type >>= fun typ ->
	    let insert_elem props =
	      printf "Finished element %s\n" n;
	      default_props typ prnt
		==> apply_pp props
		==> insert_tag n id
	    in
	    let _ = printf "Starting element %s\n" n in
	    (?/ (get_props typ)) >>= function 
		None -> sat_semi_ >>=! ~: (insert_elem [])
	      | Some props -> 
		  (?/ sat_semi_) >>= fun _ -> ~: (insert_elem props)
		      
    let sat_children_ = lit "%children;" ()
    let p_children prnt = 
      sat_children_ >>=!
      match prnt with 
      | Some prnt ->
	  ~: (modify_tag_by_name prnt (set_children true))
      | None -> failwith "Cannot set %children without parent"

    let p_nelement prnt =
      get_name >>= fun n -> 
	sat_semi_ >>=!
	match prnt with
	| None -> failwith "Cannot have nelement outside container block"
	| Some prnt -> 
	    ~: (add_parent_retro n prnt)

    let sat_container_ = lit "container" ()
    let sat_lcurl_ = lit "{" ()
    let sat_rcurl_ = lit "}" ()

    let sat_is_ = spc >>=! lit ":=" () >>=! spc

    let rec p_celement prnt =
      get_name >>= fun n -> sat_is_ >>=!
	get_id >>= fun id -> sat_container_ >>=!
	  get_cprops >>= fun cprops ->
	    let ele = apply_pp cprops (default_props `Container_t prnt) in
	    let ins = insert_tag n id ele in
	    let just_semi = sat_semi_ >>=! ~: ins
	    and has_kids =
	      sat_lcurl_ >>=!
              let _ = printf "Starting container %s\n" n in
	      (?* (p_delement (Some n))) >>= fun delems ->
		sat_rcurl_ >>=! 
		let _ = printf "Finished container %s\n" n in
		~: (apply_pp (ins::delems))
	    in
	    Cf_parser.alt [just_semi; has_kids]
    and p_delement prnt = 
      try 
	Cf_parser.alt 
	  [
	   p_velement prnt; 
	   p_celement prnt; 
	   p_nelement prnt;
	   p_children prnt; 
	 ]
      with Failure msg -> ~: (print_endline msg; fun x -> x) 
	  
    let p_statement : top_p_type = 
      get_name >>= fun n -> 
	sat_is_ >>= fun _ ->
	  get_val_any >>= fun v -> 
	    let repl x = NameMap.replace (n, v) x in
	    ~: (fun dtd -> { dtd with header = repl dtd.header})


    let p_dtype =
      get_name >>= fun n -> sat_is_ >>=!
	get_type >>= fun typ ->
	  get_tprops typ >>= fun mods ->
	    let ele = apply_pp mods (default_typed typ) in
	    let repl x = NameMap.replace (n, ele) x in
	    ~: (fun dtd -> {dtd with types = repl dtd.types})
	      

    let hblock_begin_ = 
      spc >>=! lit "declare" () >>=! spc >>=! wsp >>=! spc >>=!
      lit "header" () >>=! spc >>=! lit "{" ()
    let eblock_begin_ =
      spc >>=! lit "define" () >>=! spc >>=! wsp >>=! spc >>=!
      lit "elements" () >>=! spc >>=! lit "{" ()
    let tblock_begin_ =
      spc >>=! lit "define" () >>=! spc >>=! wsp >>=! spc >>=!
      lit "types" () >>=! spc >>=! lit "{" ()
    let sat_block_end_ = lit "}" ()
    let parse_block : top_p_type = 
      let end_block mod_list = sat_block_end_ >>=! ~:(apply_pp mod_list) in
      Cf_parser.alt 
	[ hblock_begin_ >>=! (?* p_statement) >>= end_block;
	  eblock_begin_ >>=! (?* (p_delement None)) >>= end_block;
	  tblock_begin_ >>=! (?* p_dtype) >>= end_block;
	]

    let run0 def str = 
      let cursor_ = new Cf_lexer.line_cursor "\n" in
      (Cf_seq.of_substring str 0) (* make stream of chars *)
	==> (Cf_parser.X.weave ~c:cursor_) (* line-tagged stream of chars *)
	==> (unfold parse_block)
	==> Cf_seq.first (* strip the tagging so we can use the data easily *)
	==> (Cf_seq.fold (==>) def)

    let default_dtd = run0 new_dtd default_dtd_pre_
    let parse : string -> dtd = fun str -> run0 default_dtd str
	
(******************************************************************)

	
	
    let is_base64 = function 'a'..'z' | 'A'..'Z' | '0'..'9' | '~' | '-' -> true | _ -> false
    let is_hex = function 'a'..'f' | 'A'..'F' | '0'..'9' -> true | _ -> false
	
    let get_id t name = id_of_name t name
    let get_name t id = let (name, _) = IdMap.search id t.elements in name

    let lookup t id = let (_, props) = IdMap.search id t.elements in props
    let find t name = lookup t (get_id t name)

    let find_type t name = props_type (find t name)
    let lookup_type t id = props_type (lookup t id)

    let lookup_tag_info t id = let p = lookup t id in (props_type p, p.pl)

    let get_context t prnt = IdMap.search prnt t.ctx

  end

let fn_dtd = "   
    declare header {
      DocType := \"freenet\";
    }
    define types {
      base64f := binary [ range:45; range:48..57; range:65..90; range:97..122; range:126; ]
      hex := binary [ range:48..57; range:65..70; range:97..102; ]
      htl := uint [ range 0..255; ]
      key := binary;
    }
    define elements {

    Message_ID := 11 uint;
    HTL := 12 htl;
    Key := 13 key;

    // test messages
    UID := 0100 uint;
    Freenet_URI := 0101 string;
    CHK_Header := 0102 binary;
    Freenet_Key := 0103 binary;
    Test_Chk_Headers := 0104 binary;

    testTransferSend := 0110 container { UID; }
    testTransferSendAck := 0111 container { UID; }
    testSendCHK := 0112 container {
      UID;
      Freenet_URI;
      CHK_Header;
    }
    testRequest := 0113 container {
      UID;
      Freenet_Key;
      HTL;
    }
    testDataNotFound := 0114 container { UID; }
    testDataReply := 0115 container { 
      UID; 
      Test_Chk_Headers; 
    }
    testSendCHKAck := 0116 container {
      UID;
      Freenet_URI;
    }
	  
    testDataReplyAck := 0117 container { UID; }
    testDataNotFoundAck := 0118 container { UID; }

    /* The following are the freenet messages with typed message parts
    ping = (SEND_TIME:long)
    pong = (SEND_TIME:long) 
    whoAreYou = ()
    introduce = (EXTERNAL_ADDRESS:peer, BUILD:int, FIRST_GOOD_BUILD:int)
    rejectDueToLoop = (UID:long)
    //Assimilation (?)
    joinRequest = (UID:long, JOINER:peer, TTL: int)
    joinRequestAck = (UID:long)
    joinResponse = (UID:long, PEERS: peer list)
    disconnectNotification = (REASON: string)
    requestData = (UID:long, URL:string, FORWARDERS:peer list, FILE_LENGTH:long,
	   LAST_MODOFIED:string, CHUNK_NO:int, TTL:int)
    acknowledgeRequest = (UID:long)
    requestSuccessful = (UID:long, DATA_SOURCE:peer, CACHED: bool)
    requestFailed = (UID:long, REASON:int, DESCRIPTION:string)
    //Hash search (?)
    requestHash = (UID:long, URL:string, FILE_LENGTH:long, LAST_MODIFIED:string,
		   CHUNK_NO:int, TTL:int)
    requestHashAck = (UID:long)
    //Corruption Notification
    corruptionNotification = (UID:long, URL:string, FILE_LENGTH:long, LAST_MODIFIED:string,
			      CHUNK_NO:int, IS_HASH:bool)
    packetTransmit = (UID:long, PACKET_NO:int, SENT:bitarray, DATA:buffer)
    allSent = (UID:long)
    missingPacketNotification = (UID:long, MISSING:int list)
    allRecieved = (UID:long)
    sendAborted = (UID:long, REASON:string)
    //internal only messages (?)
    testRecieveCompleted = (UID:long, SUCCESS:bool, REASON:string)
    testSendCompleted = (UID:long, SUCCESS:bool, REASON:string)
    //FNP messages
    FNPDataRequest = (UID:long, HTL:int, FREENET_ROUTING_KEY:NodeCHK)
    FNPRejectLoop = (UID:long)
    FNPRejectOverload = (UID:long)
    */
    FNP_Data_Request := 20 container [ card:*; ] {
      Message_ID; HTL; Key;
    }
    FNP_Reject_Loop := 21 container [ card:*; ] { Message_ID; }
	FNP_Reject_Overload := 22 container [ card:*; ] { Message_ID; }
    }"


module Eb_rec =
struct

  open Eb_types
  open Cf_parser.Op

  module Eb_size =
  struct
    type t = Known of Vint.t | Unknown of int (* int*7 bits of ones. *)
    let of_vint_ret = function
	Vint.Num s -> Known s
      | Vint.Reserved s -> Unknown s
	  
    let to_string = function
	Known v -> Vint.to_string v
      | Unknown len -> 
	  let ret = String.make len '\255' in
	  ret.[0] <- Char.chr (511 lsr len);
	  ret	
  end

(*
  let rec to_buffer t = 
    let buf = Buffer.create 16 in
    Buffer.add_string buf (Vint.to_string t.id);
    Buffer.add_string buf (Eb_size.to_string t.size);
    (match t.data with
	Value v ->
	  Buffer.add_string buf (val_str v)
      | Contain tl ->
	  List.iter (fun x -> Buffer.add_buffer buf (to_buffer x)) tl);
    buf

  let to_string t = Buffer.contents (to_buffer t)
 *)
(*
  let of_seq_hdr =
	    {id=eid; size=len; dat={}}
	    match Eb_dtd.lookup_type dtd eid with
		`Container_t -> 
		  ((?* (of_seq_hdr (id_width, size_width) dtd)) >>= fun tlist ->
		     ~: {id=eid; size=len; data = Contain tlist})
	      | t -> 
		  Eb_val.of_raw_seq t >>= fun v ->
		    ~: {id=eid; size=len; data=v}
 *)

  let rec limit64 n s =
    if n < Int64.zero then invalid_arg "limit64: n<0";
    lazy begin
      match Lazy.force s with
      | Cf_seq.P (hd, tl) when n > Int64.zero -> 
	  Cf_seq.P (hd, limit64 (Int64.pred n) tl)
      | _ -> Cf_seq.Z
    end

  let shift64 = 
    let rec loop n = function
      | Cf_seq.P (_, tl) when n > Int64.zero ->
	  loop (Int64.pred n) (Lazy.force tl)
      | cell -> cell 
    in
    fun n s ->
      if n < Int64.zero then invalid_arg "shift64: n<0";
      lazy (loop n (Lazy.force s))


  let get_tag (lookup:eb_id -> eb_type * Eb_dtd.Eb_params.parlev ) =
    let max_id = 4 and max_size = 8 in
    Vint.of_seq ~max:max_id >>= function
	Vint.Reserved l -> Cf_parser.nil (* id can't be a reserved vint *)
      | Vint.Num eid ->
	  Vint.of_seq ~max:max_size >>= fun vint_ret ->
	    let len = Eb_size.of_vint_ret vint_ret in
	    match lookup eid with
	      (`Container_t, pl) ->
		~: (eid, (`Container_t, pl))
	    | (#eb_value_type as typ, pl) ->
		(match len with
		  Eb_size.Unknown _ -> 
		    failwith "Cannot have unknown size non-container"
		| Eb_size.Known s ->
		    fun seq ->
		      let tl = shift64 s seq
		      and dat = eb_val_of_seq (limit64 s seq) typ in
		      Some ((eid, (dat, pl)), tl)
		)


  type ebml_header = {
      eb_ver : Eb_uint.t;
      eb_read_ver : Eb_uint.t;
      max_id : Eb_uint.t;
      max_size : Eb_uint.t;
      doctype : Eb_string.t;
      dt_ver : Eb_uint.t;
      dt_read_ver : Eb_uint.t;
    }
(*     EBML := 1a45dfa3 container [ card:+; ] {
       EBMLVersion := 4286 uint [ def:1; ]
       EBMLReadVersion := 42f7 uint [ def:1; ]
       EBMLMaxIDLength := 42f2 uint [ def:4; ]
       EBMLMaxSizeLength := 42f3 uint [ def:8; ]
       DocType := 4282 string [ range:32..126; ]
       DocTypeVersion := 4287 uint [ def:1; ]
       DocTypeReadVersion := 4285 uint [ def:1; ]
     }
*)
(*
  let get_tag_plus lookup dtd lev = 
    let get_tag' = get_tag lookup max_id max_size in
    let ctx = root_ctx dtd in
    get_tag' >>= function t1 ->
      match t1.typ with
	`Container_t -> 
	  get_tag_plus lookup max_id max_size (get_context dtd t1.id)
      | _ -> ~: (t1, None)
*)
	
  type 'a rc = eb_id * 'a
  type flat = bool * (int -> bool) * [eb_val | `Container_t]

  type tree_rec = V of eb_val | C of t list
  and t = eb_id * tree_rec

  module Ctx = Eb_dtd.Ctx
	
  let collector get_context get_rec seq = 
    let rec collect_int ctx (acc: t list) lev =
      let rec_proc =
	get_rec >>= function
	    (id, (`Container_t, pl)) when Ctx.ok ctx id pl lev ->
	      collect_int (get_context id) [] (succ lev) >>= fun dat ->
		let acc = (id, C dat) :: acc in
		collect_int (Ctx.next ctx id) acc lev
	  | (id, ((#eb_val as v), pl)) when Ctx.ok ctx id pl lev ->
	      collect_int (Ctx.next ctx id) ((id, V v)::acc) lev
	  | _ -> Cf_parser.nil
      and zero_proc = 
	if Ctx.zero ctx then
	  let (acc, tl) = Ctx.make_default (fun id v -> (id, V v)) ctx acc in
	  collect_int tl acc lev
	else
	  failwith "Expecting id %s" (Vint.to_hex_string (Ctx.expectid ctx))
      in
      Cf_parser.alt [rec_proc; zero_proc]
    in
    let toplev_elem = collect_int (get_context Ctx.root_ctx_id) [] 1 >>= fun cl -> ~: (C cl) in
    Cf_parser.unfold toplev_elem seq
      
      
(* TODO: handle non 4,8 data sequences *)
  let of_seq dtd seq = 
    let get_rec = get_tag (Eb_dtd.lookup_tag_info dtd) in
    collector (Eb_dtd.get_context dtd) get_rec seq
      
(*
  let val_str = function
      Int_v v | Uint_v v -> Vint.to_string v
    | Float_v (F0) -> ""
    | Float_v (F4 v) -> Crypto.string_of_i32 (Int32.bits_of_float v)
    | Float_v (F8 v) -> Crypto.string_of_i64 (Int64.bits_of_float v)
    | Float_v (F10 v) -> "\000\000" ^ Crypto.string_of_i64 (Int64.bits_of_float v)
    | String_v s -> s
    | Ustring_v us -> us
    | Date_v d -> Crypto.string_of_i64 d
    | Binary_v b -> b
 *)  
(*    let data_type = lookup eid dtd in *)
    
end



let main () = Eb_dtd.parse fn_dtd

let _ = main ()

