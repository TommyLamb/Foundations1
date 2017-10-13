

fun translateV (ID x) = IID x
  | translateV (LAM (x, y)) = ILAM(x, (translateV y))
  | translateV (APP (x, y)) = IAPP ((translateV y), (translateV x)); (* Note change of order *)

fun combinatorReduction (CID x) (COM y) = 

fun translateT (IID x) = CID x
  | translateT (IAPP(x, y)) = CAPP ((translateT y), (translateT x))
  | translateT (ILAM (x, y)) = 
