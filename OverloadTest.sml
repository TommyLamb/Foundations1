signature LAMDA = sig
	val printEXP : int -> int
end

structure Lamda : LAMDA = struct
	val printEXP = fn x => x+1
end

signature COM = sig
	val printEXP : string -> string
end

structure Com : COM = struct
	val printEXP = fn x => x
end

_overload printEXP : ('a -> 'a) as Com.printEXP and Lamda.printEXP
