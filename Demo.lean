import WingBijection.Checked

open WingBijection Finset

namespace Demo

def point (n k : ℕ) : Cube n := fun i => k.testBit i.val

def code {n : ℕ} (x : Cube n) : ℕ :=
  ∑ i : Fin n, if x i then 2 ^ i.val else 0

def maskAt (rows : List (ℕ × ℕ)) (k : ℕ) : ℕ :=
  ((rows.find? fun row => row.1 = k).map Prod.snd).getD 0

/-- This front end takes only ordinary finite data; validation supplies the proof
argument of the verified constructor. -/
def solve (n : ℕ) (codes masks : List ℕ) :
    Option (List (ℕ × ℕ) × List ℕ × List ℕ × Bool) :=
  let O := (codes.map (point n)).toFinset
  let A : Cube n → Finset (Fin n) := fun x =>
    univ.filter fun i => (maskAt (codes.zip masks) (code x)).testBit i.val
  match checkedConstruct n O A with
  | none => none
  | some τ =>
    let xs := pointList n O
    let pairs := xs.map fun x => (code x.val, code (τ x).val)
    let keep := (List.finRange n).map fun j => xs.countP fun x => (τ x).val j = x.val j
    let boundary := (List.finRange n).map fun j =>
      (O.filter fun x => Function.update x j (!x j) ∉ O).card
    let checks := decide ((pairs.map Prod.snd).Nodup) &&
      pairs.all (fun row => (row.1 ^^^ row.2) &&& maskAt (codes.zip masks) row.1 =
        maskAt (codes.zip masks) row.1) &&
      (keep.zip boundary).all (fun row => row.1 ≤ row.2) &&
      xs.all (fun x => τ.symm (τ x) = x ∧ τ (τ.symm x) = x)
    some (pairs, keep, boundary, checks)

def parseNumbers (s : String) : Option (List ℕ) :=
  if s = "" then some [] else (s.splitOn ",").mapM String.toNat?

def validEncoding (n : ℕ) (codes masks : List ℕ) : Bool :=
  codes.length = masks.length && decide codes.Nodup &&
    codes.all (fun k => k < 2 ^ n) && masks.all (fun k => k < 2 ^ n)

def run (n : ℕ) (codes masks : List ℕ) : IO UInt32 := do
  if !validEncoding n codes masks then
    IO.eprintln "Invalid encoding: use distinct n-bit points and one n-bit wing mask per point."
    return 2
  match solve n codes masks with
  | none =>
    IO.eprintln "Invalid wing assignment: some subcube leaves O."
    return 1
  | some (pairs, keep, boundary, checks) =>
    IO.println s!"n = {n}; |O| = {codes.length}"
    IO.println s!"(point, tau(point)): {pairs}"
    IO.println s!"agreements: {keep}"
    IO.println s!"boundary:   {boundary}"
    IO.println s!"output checks: {checks}"
    return if checks then 0 else 3

end Demo

def main (args : List String) : IO UInt32 :=
  match args with
  | [] => Demo.run 4 [0,1,4,5,7,12,13,14,15] [5,5,5,9,10,3,10,3,3]
  | [n, codes, masks] =>
    match n.toNat?, Demo.parseNumbers codes, Demo.parseNumbers masks with
    | some n, some codes, some masks => Demo.run n codes masks
    | _, _, _ => do
      IO.eprintln "Expected natural numbers, with points and masks separated by commas."
      return 2
  | _ => do
    IO.eprintln "Usage: lake exe wingDemo [n points_csv wing_masks_csv]"
    return 2
