module type VectorS = sig
  type 'a t 

  val make : int -> 'a -> 'a t
  val create : unit -> 'a t
  val shrink : 'a t -> int -> unit
  val is_empty : 'a t -> bool
  val size : 'a t -> int
  val pop : 'a t -> 'a option
  val push : 'a t -> 'a -> unit
  val set : 'a t -> int -> 'a -> unit
  val get : 'a t -> int -> 'a
  val last : 'a t -> 'a
  val iter_from : ('a -> unit) -> 'a t -> int -> unit
  val iter : ('a -> unit) -> 'a t -> unit

end

module type SetS = sig
  type 'a t 

  val create : unit -> 'a t
  val filter : ('a -> bool) -> 'a t -> unit
  val is_empty : 'a t -> bool
  val size : 'a t -> int
  val push : 'a t -> 'a -> unit
  val iter : ('a -> unit) -> 'a t -> unit
end

module Vector : VectorS
module VSet : SetS
