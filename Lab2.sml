(* This leftmost reduces the given term, returning a LEXP List listing each step in the order they are carried out *)

fun leftmost (ID v) = [ID v]
  | leftmost (LAM (v, a)) =
	 if has_redex a then
		(LAM (v, a))::addlam v (leftmost a)
	else
		[LAM (v, a)]
  | leftmost (APP (a, b)) =
	if is_redex (APP (a, b)) then
		(APP (a, b))::(leftmost(red (APP(a, b))))
	else if has_redex a then
		(APP (a, b))::(leftmost(APP((red a), b)))
	else if has_redex b then
		(APP (a, b))::(leftmost(APP(a, (red b))))
	else
		[APP (a, b)];
