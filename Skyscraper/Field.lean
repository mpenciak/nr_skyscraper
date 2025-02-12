import Mathlib
import Skyscraper.Util

namespace Skyscraper

structure Field (_p : Nat) where
  val : Nat
deriving Repr

variable {p : Nat}

instance : Coe Nat (Field p) where
  coe x := ⟨x % p⟩

instance {n} : OfNat (Field p) n where
  ofNat := n

instance : Add (Field p) where
  add x y := (x.val + y.val) % p

instance : Mul (Field p) where
  mul x y := (x.val * y.val) % p

namespace Field

def fromLeBytes (b : ByteArray) : Field p := b.toNat

def toLeBytes (f : Field p) : ByteArray :=
  let bytes := ByteArray.mkZero 32
  f.val.toByteArray.copySlice 0 bytes 0 32

end Field

end Skyscraper
