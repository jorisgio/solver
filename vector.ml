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

module BaseVector = struct
  type 'a t = { mutable data : 'a array; mutable size : int }

  let make cap elem = { data =  Array.make cap elem; size = 0 }

  let create () = { data = [| |]; size = 0 }


  let is_empty vec = vec.size = 0

  let size vec = vec.size

  let is_full vec = vec.size = Array.length vec.data

  let grow vec factor elem =
	let newcap = 
	  Array.length vec.data * factor
	in
	vec.data <- Array.init newcap (fun i -> if i < vec.size then vec.data.(i) else elem) 


  let push vec elem = 
	if is_full vec then
	  grow vec 2 elem
	else 
	  vec.data.(vec.size) <- elem;
	vec.size <- vec.size + 1

  let iter_from f vec idx = 
	for i = idx to vec.size - 1 do
	  f (vec.data.(i))
	done

  let iter f vec = iter_from f vec 0

end

module VSet = struct 
  include BaseVector

  let filter f vec =
	let i = ref 0 in
	while !i < vec.size do
	  if f vec.data.(!i) then
		incr i
	  else 
		begin
		  while vec.size > !i && not (f vec.data.(vec.size - 1)) do 
			vec.size <- vec.size - 1
		  done;
		  if vec.size > !i then 
			begin
			  vec.data.(!i) <- vec.data.(vec.size - 1);
			  vec.size <- vec.size - 1
			end
		end
	done

end

module Vector = struct
  include BaseVector

  let shrink vec size = assert (size >= 0 && size <= vec.size); vec.size <- size

  let pop vec = 
	if vec.size > 0 then 
	  (vec.size <- vec.size - 1; Some vec.data.(vec.size))
	else 
	  None

  let set vec i elem = 
	assert (i >= 0 && i < vec.size);
	vec.data.(i) <- elem

  let get vec i =
	assert (i >= 0 && i < vec.size);
	vec.data.(i)

  let last vec = vec.data.(vec.size - 1)
end
