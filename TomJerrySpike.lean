--------------------------PRE-ESTABLISHED STRATEGY--------------------------
structure Tom_codes where (code : List (Fin 2)) (secret_k : Nat)

def Jerry (code : List (Fin 2)) : Nat :=
  let ones_pos : List Nat :=
    ((List.range code.length).zip code |>.filter (fun (_, b) => b != 0)).map (·.1)
  ones_pos.foldl (· ^^^ ·) 0

def Spike (x : Tom_codes)  : List (Fin 2) :=
  let flip_code :=
    x.code.mapIdx (fun idx b => if idx == x.secret_k then (if b == 0 then 1 else 0) else b)
  let flip_pos : Nat := Jerry flip_code
  x.code.mapIdx (fun idx b => if idx == flip_pos then (if b == 0 then 1 else 0) else b)

----------------------------------------------------------------------------
-------------------------------- TESTING -----------------------------------
----------------------------------------------------------------------------

def Tom : Tom_codes :=
  { code := [0, 1, 0, 1, 1, 1, 0, 1, 0, 1, 1, 0, 1, 0, 1, 0], secret_k := 7 }

#eval Tom.code
#eval Spike Tom
#eval Jerry (Spike Tom)
