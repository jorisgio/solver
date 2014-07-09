let findi f ar start = 
  let rec loop ar f last = function
	| i when i = last -> None 
    | i -> if f ar.(i) then Some i else loop ar f last (i + 1)
  in
  let last = 
	(Array.length ar) - 1
  in
  if start < 0 || start > last then
	None
  else
	loop ar f last start
