def Nat.toByteArray (n : Nat) : ByteArray :=
  aux ⟨#[]⟩ n
where
  aux (acc : ByteArray) (n : Nat) : ByteArray :=
    if h : n == 0 then acc else
      have : n ≠ 0 := Ne.symm (ne_of_apply_ne (fun n => n == 0) fun a => h (id (Eq.symm a)))
      have : 0 < n := zero_lt_of_ne_zero this
      have : n / 256 < n := Nat.div_lt_self this (by decide)
      aux (acc.push (UInt8.ofNat (n % 256))) (n / 256)

def ByteArray.toNat (b : ByteArray) : Nat :=
  b.foldl (fun acc x => acc * 256 + x.toNat) 0 -- TODO: This isn't right, this is Big Endian :(

def UInt8.not (a : UInt8) : UInt8 := ⟨a.toBitVec.not⟩

def UInt8.rotateLeft (a : UInt8) (n : Nat) : UInt8 := ⟨a.toBitVec.rotateLeft n⟩

prefix:max "!!!" => UInt8.not

