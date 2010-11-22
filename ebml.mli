module Vint :
sig
  type t
  val compare : t -> t -> int

end

module Eb_types :
sig
  module Eb_int : Map.OrderedType
  module Eb_uint : Map.OrderedType
  module Eb_float : sig 
    type t = 
	F0 
      | F4 of float 
      | F8 of float 
      | F10 of float (* only has 8 bytes of precision *)
    val to_string : t -> string
    val of_seq : char Cf_seq.t -> t
  end
  module Eb_string : sig
    type t = string (* unicode (UTF-8) string *)
  end
  module Eb_date : Map.OrderedType
(*: sig
    include Int64 (* nanoseconds to the millennium *)
  end *)
  module Eb_binary : sig
    type t = string (* octet sequence - one byte per character *)
  end

  type eb_value_type = 
      [ `Int_t 
      | `Uint_t 
      | `Float_t 
      | `String_t 
      | `Date_t 
      | `Binary_t]
	
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
	
(*
  type eb_id = Vint.t
      
  type name = string
*)
end
