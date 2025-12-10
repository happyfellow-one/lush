namespace Lush.Crypto.SHA

open Std
open BitVec

-- We implement just the SHA-256 version.

def paddingNoLength (length : Nat) (hlen : length < 2^64) :
    Σ n, BitVec n ×' ((length + n) % 512 = 448) :=
  let n :=
    if length % 512 < 448
    then 448 - (length % 512)
    else 448 + (512 - length % 512)
  have n_not_zero : n > 0 := by grind
  let b : BitVec n := BitVec.or (BitVec.twoPow n (n - 1)) (BitVec.zero n)
  let prf : (length + n) % 512 = 448 := by grind
  ⟨n, b, prf⟩

def padding (length : Nat) (hlen : length < 2^64) :
    Σ n, BitVec n ×' ((length + n) % 512 = 0) :=
  let ⟨n, b, h⟩ := paddingNoLength length hlen
  let lenBv := BitVec.ofNat 64 length
  have h' : (length + n + 64) % 512 = 0 := by grind
  ⟨n + 64, BitVec.append b lenBv, h'⟩

def shaCh (x y z : BitVec 32) : BitVec 32 := (x &&& y) ||| (~~~x &&& z)
def shaMaj (x y z : BitVec 32) : BitVec 32 := (x &&& y) ^^^ (x &&& z) ^^^ (y &&& z)

def shaSigma₀ (x : BitVec 32) : BitVec 32 :=
  BitVec.rotateRight x 2
  ^^^ BitVec.rotateRight x 13
  ^^^ BitVec.rotateRight x 22

def shaSigma₁ (x : BitVec 32) : BitVec 32 :=
  BitVec.rotateRight x 6
  ^^^ BitVec.rotateRight x 11
  ^^^ BitVec.rotateRight x 25

def shasigma₀ (x : BitVec 32) : BitVec 32 :=
  BitVec.rotateRight x 7
  ^^^ BitVec.rotateRight x 18
  ^^^ BitVec.ushiftRight x 3

def shasigma₁ (x : BitVec 32) : BitVec 32 :=
  BitVec.rotateRight x 17
  ^^^ BitVec.rotateRight x 19
  ^^^ BitVec.ushiftRight x 10

def shaK : Array (BitVec 32) :=
  #[ 0x428a2f98, 0x71374491, 0xb5c0fbcf, 0xe9b5dba5
   , 0x3956c25b, 0x59f111f1, 0x923f82a4, 0xab1c5ed5
   , 0xd807aa98, 0x12835b01, 0x243185be, 0x550c7dc3
   , 0x72be5d74, 0x80deb1fe, 0x9bdc06a7, 0xc19bf174
   , 0xe49b69c1, 0xefbe4786, 0x0fc19dc6, 0x240ca1cc
   , 0x2de92c6f, 0x4a7484aa, 0x5cb0a9dc, 0x76f988da
   , 0x983e5152, 0xa831c66d, 0xb00327c8, 0xbf597fc7
   , 0xc6e00bf3, 0xd5a79147, 0x06ca6351, 0x14292967
   , 0x27b70a85, 0x2e1b2138, 0x4d2c6dfc, 0x53380d13
   , 0x650a7354, 0x766a0abb, 0x81c2c92e, 0x92722c85
   , 0xa2bfe8a1, 0xa81a664b, 0xc24b8b70, 0xc76c51a3
   , 0xd192e819, 0xd6990624, 0xf40e3585, 0x106aa070
   , 0x19a4c116, 0x1e376c08, 0x2748774c, 0x34b0bcb5
   , 0x391c0cb3, 0x4ed8aa4a, 0x5b9cca4f, 0x682e6ff3
   , 0x748f82ee, 0x78a5636f, 0x84c87814, 0x8cc70208
   , 0x90befffa, 0xa4506ceb, 0xbef9a3f7, 0xc67178f2
   ]

structure ShaBlock where
  block : Array (BitVec 32)
  hlen : block.size = 16 := by grind

structure MessageSchedule where
  schedule : Array (BitVec 32)
  hlen : schedule.size = 64 := by grind

def messageSchedule (block : ShaBlock) : MessageSchedule :=
  have hblocklen : block.block.size = 16 := block.hlen
  Id.run do
    let mut schedule : { a : Array (BitVec 32) // a.size = 64 } :=
      ⟨Array.replicate 64 (BitVec.zero 32), by trivial⟩
    for x in List.finRange 16 do
      schedule := ⟨schedule.val.set x (block.block[x]), by grind⟩
    for x' in List.finRange (64 - 16) do
      let x := x'.val + 16
      let val :=
        shasigma₁ (schedule.val[x-2])
        + schedule.val[x-7]
        + shasigma₀ (schedule.val[x-15])
        + schedule.val[x-16]
      schedule := ⟨schedule.val.set x val, by grind⟩
    return ⟨schedule, by grind⟩

structure ShaState where
  hash : Array (BitVec 32)
  hhashlen : hash.size = 8 := by grind

set_option diagnostics true

def shaRound (state : ShaState) (block : ShaBlock) : ShaState :=
  let schedule := messageSchedule block
  let working := state.hash
  let f (working : { a : Array (BitVec 32) // a.size = 8 }) (i : Fin 64) :=
    let ⟨working, hworkinglen⟩ := working
    have hschedulelen := schedule.hlen
    let T1 :=
      working[7]
      + shaSigma₁ working[4]
      + shaCh working[4] working[5] working[6]
      + shaK[i.val]
      + schedule.schedule[i.val]
    let T2 :=
      shaSigma₀ working[0]
      + shaMaj working[0] working[1] working[2]
    let working :=
      #[ T1 + T2
       , working[0]
       , working[1]
       , working[2]
       , working[3] + T1
       , working[4]
       , working[5]
       , working[6]
      ]
    ⟨working, by trivial⟩
  let working := (List.finRange 64).foldl f ⟨working, state.hhashlen⟩
  have hworkinglen : working.val.size = 8 := by sorry
  let hash :=
    have hhashlen : state.hash.size = 8 := state.hhashlen
    Array.mapFinIdx state.hash (fun i a hi => a + working.val[i])
  have hhashlen : hash.size = 8 := by unfold hash; simp; exact state.hhashlen
  { hash := hash, hhashlen := hhashlen }

end Lush.Crypto.SHA
