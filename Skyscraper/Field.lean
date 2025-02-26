import Lampe

open Lampe

def p := 21888242871839275222246405745257275088548364400416034343698204186575808495617 - 1

axiom pPrime : Nat.Prime (p + 1) -- TODO: Should be able to prove this at some point

namespace Skyscraper

abbrev bnField := Fp ⟨p, pPrime⟩

instance : ToString bnField where
  toString b := s!"{b.val}"

instance : Repr bnField where
  reprPrec b _ := toString b

namespace bnField

def fromLeBytes (b : List.Vector (U 8) 32) : bnField :=
  let rec aux (b : List (U 8)) (acc : bnField) : bnField :=
    match b with
    | [] => acc
    | b :: bs => aux bs (256 * acc + b.toNat)
  aux b.toList 0

def toLeBytes (f : bnField) : List.Vector (U 8) 32 := ⟨padEnd 32 (Lampe.toLeBytes f), by
  unfold padEnd
  simp
  have : (Lampe.toLeBytes f).length <= 32 := by sorry -- TODO: This could take some lemmas
  simp only [this, add_tsub_cancel_of_le]⟩

end bnField

end Skyscraper
