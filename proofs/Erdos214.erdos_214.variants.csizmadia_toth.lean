import FormalConjectures.ErdosProblems.«214»

-- Problem: Erdős Problem 214 — Csizmadia–Tóth bound
-- Upstream: formal-conjectures FormalConjectures/ErdosProblems/214.lean (declaration Erdos214.erdos_214.variants.csizmadia_toth)
-- The statement k ≤ 7 is due to G. Csizmadia and G. Tóth (J. Combin. Theory Ser. A, 1994).

/-
Construction. S is the union of the open disks of radius 1/2 centred at the lattice points
(2a+b, 7b/4), a b integers; distinct centres are at distance at least 2, so S has no two points
at distance 1. K is the centre (0,0) together with seven points close to a regular heptagon of
radius 4/5. Take a congruent copy p of K. The image of the centre lies in a lattice triangle
with vertices A, A+(2,0), A+(1,±7/4). Pull the triangle back to the frame of K with the
isometry carrying p to K: the centre then has barycentric coordinates (s,t) in a triangle with
edge vectors e = 2(u,v), f = (u,v) ± (7/4)(-v,u), u^2+v^2 = 1. A finite certificate (a
subdivision of the (s,t,direction) parameter box, checked by kernel evaluation) shows that
some vertex of the triangle is within distance 1/2 of some point of K, so the corresponding
point of the copy lies in S.
The direction (u,v) is written as ±((1-x^2)/(1+x^2), 2x/(1+x^2)) with x in [-1,1]; on an
interval of x the arc lies in the triangle formed by its end points and the meeting point of
the end tangents, and the squared distance is affine in (u,v) and convex in (s,t), so it is
enough to test the corners.
-/

open scoped EuclideanGeometry Congruent

namespace OMA214C

inductive Tr where
  | l : ℕ → Tr
  | q : ℕ → Tr
  | k : Tr
  | s : Tr → Tr → Tr
  | t : Tr → Tr → Tr
  | j : Tr → Tr → Tr

def kxn : ℕ → ℤ
  | 0 => 0 | 1 => 80 | 2 => 50 | 3 => -18 | 4 => -72 | 5 => -72 | 6 => -18 | 7 => 50 | _ => 0

def kyn : ℕ → ℤ
  | 0 => 0 | 1 => 0 | 2 => 63 | 3 => 78 | 4 => 35 | 5 => -35 | 6 => -78 | 7 => -63 | _ => 0

def amn : ℕ → ℤ
  | 1 => 1 | _ => 0

def bmn : ℕ → ℤ
  | 2 => 1 | _ => 0

def Dz (sg A B U V Z k1 k2 : ℤ) : ℤ :=
  10000 * Z * (64 * A * A + 64 * A * B + 65 * B * B)
    - 409600 * ((64 * A + 32 * B) * (k1 * U + k2 * V) + 56 * sg * B * (k2 * U - k1 * V))
    + 268435456 * Z * (k1 * k1 + k2 * k2)

def ok1 (sg A B U V Z k1 k2 : ℤ) : Bool := Dz sg A B U V Z k1 k2 < 671088640000 * Z

def okc (sg ep : ℤ) (c : ℕ) (S T j0 j1 : ℤ) : Bool :=
  ok1 sg (amn (c / 8) * 4096 - S) (bmn (c / 8) * 4096 - T) (ep * (4096 - j0 * j0)) (ep * (128 * j0))
      (4096 + j0 * j0) (kxn (c % 8)) (kyn (c % 8)) &&
  ok1 sg (amn (c / 8) * 4096 - S) (bmn (c / 8) * 4096 - T) (ep * (4096 - j1 * j1)) (ep * (128 * j1))
      (4096 + j1 * j1) (kxn (c % 8)) (kyn (c % 8)) &&
  ok1 sg (amn (c / 8) * 4096 - S) (bmn (c / 8) * 4096 - T) (ep * (4096 - j0 * j1)) (ep * (64 * (j0 + j1)))
      (4096 + j0 * j1) (kxn (c % 8)) (kyn (c % 8))

def leafok (sg ep : ℤ) (c : ℕ) (S0 S1 T0 T1 j0 j1 : ℤ) : Bool :=
  decide (j0 < j1) && decide (-64 ≤ j0) && decide (j1 ≤ 64) && decide (0 < 4096 + j0 * j1) &&
  okc sg ep c S0 T0 j0 j1 && okc sg ep c S0 T1 j0 j1 && okc sg ep c S1 T0 j0 j1 && okc sg ep c S1 T1 j0 j1

def chk (sg ep : ℤ) : Tr → ℤ → ℤ → ℤ → ℤ → ℤ → ℤ → Bool
  | .l c, S0, S1, T0, T1, j0, j1 => leafok sg ep c S0 S1 T0 T1 j0 j1
  | .q c, S0, _, T0, _, j0, j1 => decide (4096 ≤ S0 + T0) && leafok sg ep c S0 S0 T0 T0 j0 j1
  | .k, S0, _, T0, _, _, _ => decide (4096 < S0 + T0)
  | .s a b, S0, S1, T0, T1, j0, j1 =>
      chk sg ep a S0 ((S0 + S1) / 2) T0 T1 j0 j1 && chk sg ep b ((S0 + S1) / 2) S1 T0 T1 j0 j1
  | .t a b, S0, S1, T0, T1, j0, j1 =>
      chk sg ep a S0 S1 T0 ((T0 + T1) / 2) j0 j1 && chk sg ep b S0 S1 ((T0 + T1) / 2) T1 j0 j1
  | .j a b, S0, S1, T0, T1, j0, j1 =>
      chk sg ep a S0 S1 T0 T1 j0 ((j0 + j1) / 2) && chk sg ep b S0 S1 T0 T1 ((j0 + j1) / 2) j1


open Tr in
def trpp0 : Tr := t (s (t (j (s (s (t (l 0) (t (t (l 0) (l 4)) (l 4))) (s (t (s (l 0) (t (l 0) (l 3))) (j (l 3) (l 4))) (s (t (l 3) (t (l 3) (l 4))) (l 3)))) (t (l 3) (s (s (l 3) (t (l 3) (l 14))) (l 14)))) (t (s (s (l 0) (t (s (l 0) (s (s (l 0) (s (l 0) (l 3))) (l 3))) (s (t (l 0) (l 4)) (l 4)))) (j (s (l 3) (s (l 3) (j (l 3) (s (l 3) (l 15))))) (s (t (l 3) (l 4)) (s (t (l 3) (l 4)) (l 15))))) (s (s (t (s (l 0) (l 4)) (s (t (s (l 0) (l 4)) (l 4)) (l 4))) (l 4)) (s (s (l 4) (s (l 4) (s (l 4) (s (l 4) (s (l 4) (t (t (j (l 3) (l 4)) (l 4)) (l 4))))))) (j (s (j (s (t (l 3) (l 14)) (l 14)) (s (l 4) (s (j (l 14) (l 4)) (l 14)))) (l 14)) (s (l 4) (t (t (l 15) (j (l 14) (l 15))) (s (s (j (l 14) (l 4)) (l 14)) (l 14))))))))) (s (t (s (l 4) (s (l 4) (s (l 4) (s (l 4) (t (l 4) (j (l 17) (l 4))))))) (s (j (l 4) (t (l 4) (l 17))) (j (l 17) (t (l 4) (s (l 17) (s (l 17) (j (l 17) (j (l 17) (l 18))))))))) (j (j (t (s (t (s (l 3) (l 14)) (l 17)) (s (l 14) (s (l 14) (s (l 14) (s (l 14) (t (l 14) (l 13))))))) (s (l 17) (s (l 17) (s (s (t (l 17) (l 13)) (l 13)) (l 13))))) (t (s (s (s (l 4) (l 14)) (l 14)) (l 14)) (s (l 17) (t (s (l 14) (s (l 14) (j (t (l 14) (l 13)) (l 14)))) (s (t (j (s (l 17) (s (l 17) (l 18))) (l 14)) (l 18)) (l 18)))))) (s (t (s (l 4) (j (s (s (l 4) (l 14)) (l 14)) (s (l 4) (t (l 4) (l 14))))) (s (j (s (l 17) (t (l 14) (s (l 17) (t (l 14) (l 18))))) (t (s (l 4) (t (l 4) (l 18))) (l 18))) (s (t (l 14) (t (l 14) (l 18))) (l 14)))) (s (s (s (s (t (t (j (l 14) (l 4)) (l 14)) (l 14)) (l 14)) (l 14)) (l 14)) (t (l 14) (l 18))))))) (t (s (t (j (l 14) (t (s (l 15) (s (l 15) (s (l 15) (s (l 15) (t (l 15) (t (l 15) (l 8))))))) (s (j (t (l 15) (l 14)) (l 15)) (t (j (l 14) (j (l 14) (l 15))) (l 14))))) (s (s (s (t (t (j (l 14) (j (l 14) (l 15))) (l 14)) (l 14)) (l 14)) (l 14)) (s (l 14) (s (t (l 14) (t (l 14) (j (l 13) (l 14)))) (t (l 14) (j (t (j (l 13) (l 14)) (l 13)) (l 14))))))) (t (s (s (s (s (s (s (s (s (s (s (t (t (t (t (t (t (t (t (t (j (l 14) (l 15)) (l 8)) (l 8)) (l 8)) (l 8)) (l 8)) (l 8)) (l 8)) (l 8)) (l 8)) (l 8)) (l 8)) (l 8)) (l 8)) (l 8)) (l 8)) (l 8)) (l 8)) (l 8)) (l 8)) (s (s (s (s (s (t (l 8) (j (l 13) (l 14))) (l 8)) (l 8)) (l 8)) (l 8)) (q 8)))) (s (j (s (t (t (s (l 14) (j (l 13) (l 14))) (j (l 13) (s (l 14) (l 13)))) (s (s (s (s (t (t (j (l 13) (l 14)) (l 13)) (l 13)) (l 13)) (l 13)) (l 13)) (l 13))) (s (s (s (s (t (t (t (l 14) (l 13)) (l 13)) (q 13)) (l 13)) (l 13)) (l 13)) (l 13))) (s (t (l 14) (j (l 18) (j (l 18) (l 14)))) (t (j (t (s (l 14) (s (l 14) (l 13))) (s (s (l 14) (l 13)) (q 13))) (s (l 14) (t (l 14) (q 14)))) (q 14)))) (s (s (s (s (s (s (s (s (s (s (t (t (t (t (t (t (t (t (t (t (j (q 13) (q 14)) (k)) (k)) (k)) (k)) (k)) (k)) (k)) (k)) (k)) (k)) (k)) (k)) (k)) (k)) (k)) (k)) (k)) (k)) (k)) (k))))) (s (t (s (s (s (s (s (s (s (t (t (j (l 4) (l 17)) (l 17)) (l 17)) (l 17)) (l 17)) (l 17)) (l 17)) (s (l 17) (s (l 17) (t (l 17) (t (l 17) (t (l 17) (l 16))))))) (t (s (l 17) (j (l 17) (j (l 17) (l 18)))) (j (s (l 17) (j (s (l 17) (s (l 17) (t (l 17) (l 18)))) (t (l 17) (l 18)))) (s (j (s (l 17) (t (l 17) (l 18))) (l 18)) (l 18))))) (s (j (t (s (l 17) (j (s (l 17) (t (l 17) (l 18))) (s (t (l 17) (l 18)) (l 18)))) (s (s (t (s (l 17) (l 18)) (l 18)) (l 18)) (l 18))) (s (s (s (s (t (j (l 17) (l 18)) (l 18)) (l 18)) (l 18)) (l 18)) (l 18))) (t (s (s (t (t (j (j (l 17) (l 18)) (l 18)) (l 18)) (l 18)) (l 18)) (l 18)) (q 18)))) (s (t (t (t (t (t (t (t (t (t (t (s (s (l 17) (l 16)) (s (l 16) (s (l 16) (l 18)))) (s (s (l 17) (l 16)) (s (l 16) (s (l 16) (l 18))))) (s (s (l 17) (l 16)) (s (l 16) (s (l 16) (l 18))))) (s (s (l 17) (l 16)) (s (l 16) (s (l 16) (l 18))))) (s (l 16) (s (l 16) (s (l 16) (l 18))))) (l 16)) (l 16)) (l 16)) (l 16)) (l 16)) (s (l 16) (q 16))) (q 18))) (q 18))

open Tr in
def trpp1 : Tr := t (s (t (j (s (s (t (l 0) (t (s (l 0) (s (l 0) (t (l 0) (j (l 4) (l 5))))) (s (l 5) (j (l 4) (l 5))))) (s (t (t (l 0) (l 4)) (s (s (s (t (l 4) (j (l 4) (l 5))) (l 4)) (l 4)) (l 4))) (l 4))) (s (l 4) (t (l 4) (l 15)))) (j (s (t (s (l 0) (s (s (l 0) (s (s (s (l 0) (s (l 0) (t (l 0) (t (l 0) (l 5))))) (s (t (l 0) (t (l 0) (l 5))) (l 4))) (l 4))) (l 4))) (s (t (s (l 0) (l 5)) (l 5)) (l 5))) (t (s (l 4) (s (l 4) (s (l 4) (s (l 4) (t (l 4) (t (l 4) (l 15))))))) (s (j (t (l 4) (s (l 5) (l 15))) (l 5)) (s (t (t (s (l 4) (s (l 4) (l 15))) (s (s (t (l 4) (l 15)) (l 15)) (l 15))) (l 15)) (l 15))))) (t (s (s (l 0) (t (s (l 0) (t (s (l 0) (l 4)) (j (l 4) (l 5)))) (s (s (l 0) (l 5)) (l 5)))) (s (t (l 4) (l 5)) (s (t (s (l 4) (l 9)) (s (l 5) (t (l 9) (s (l 5) (l 9))))) (l 9)))) (s (s (s (t (l 0) (t (s (l 0) (l 5)) (j (l 5) (l 6)))) (l 5)) (l 5)) (s (l 5) (s (s (l 5) (s (l 5) (t (l 5) (j (l 15) (l 5))))) (t (j (j (l 15) (t (l 9) (l 15))) (l 9)) (s (j (l 15) (t (l 5) (l 15))) (l 15))))))))) (s (j (j (s (s (l 5) (t (l 5) (j (t (s (l 5) (l 4)) (l 17)) (s (l 5) (s (l 5) (t (l 5) (t (l 5) (l 18)))))))) (t (l 4) (t (j (s (l 4) (t (l 4) (l 18))) (t (s (s (l 5) (j (l 4) (l 18))) (l 18)) (s (s (s (l 5) (l 18)) (l 18)) (l 18)))) (s (j (s (l 17) (l 18)) (l 18)) (l 18))))) (s (l 5) (t (j (j (s (l 5) (l 4)) (s (l 5) (t (l 4) (s (l 5) (l 18))))) (l 5)) (s (t (s (l 5) (l 18)) (l 18)) (l 18))))) (t (l 5) (t (s (j (l 5) (l 18)) (l 5)) (s (l 18) (s (l 18) (j (l 18) (j (l 18) (j (s (l 18) (l 19)) (l 19))))))))) (j (t (t (s (j (l 4) (j (s (l 4) (l 15)) (t (s (l 4) (l 15)) (l 18)))) (j (t (s (l 4) (j (l 14) (l 15))) (j (j (j (l 14) (l 18)) (l 18)) (s (l 18) (l 15)))) (l 15))) (j (s (s (s (l 4) (t (l 4) (l 18))) (s (t (l 4) (l 18)) (l 18))) (l 18)) (s (l 18) (t (l 15) (j (j (l 18) (l 15)) (l 15)))))) (s (l 18) (s (s (l 18) (s (l 18) (t (l 18) (t (s (l 18) (l 14)) (l 14))))) (s (t (s (j (l 14) (j (l 18) (j (l 18) (l 15)))) (t (j (l 14) (j (l 14) (l 15))) (l 14))) (l 14)) (l 14))))) (s (t (j (s (s (l 5) (t (l 5) (l 15))) (l 15)) (s (l 5) (s (l 5) (t (l 5) (t (l 5) (l 15)))))) (s (j (l 18) (t (t (l 5) (j (s (l 5) (l 15)) (l 19))) (s (s (j (l 18) (l 19)) (l 19)) (l 19)))) (t (s (s (s (s (s (s (s (t (j (l 15) (l 5)) (l 15)) (l 15)) (l 15)) (l 15)) (l 15)) (l 15)) (l 15)) (l 15)) (t (j (j (l 18) (l 15)) (l 19)) (s (j (j (l 18) (l 19)) (l 19)) (l 19)))))) (t (s (s (t (j (l 15) (t (l 5) (l 15))) (l 15)) (l 15)) (l 15)) (t (l 15) (s (t (t (l 15) (l 19)) (l 19)) (l 19)))))))) (t (s (s (j (s (l 15) (t (l 15) (t (l 15) (j (l 14) (l 15))))) (t (j (j (s (s (l 4) (l 15)) (l 15)) (t (l 9) (l 15))) (l 9)) (s (t (j (l 15) (t (l 9) (l 15))) (l 15)) (l 15)))) (s (t (j (l 15) (j (l 15) (l 9))) (j (j (t (t (l 15) (l 14)) (l 14)) (s (l 15) (s (l 15) (s (l 15) (t (l 15) (t (l 15) (l 14))))))) (l 15))) (s (t (j (l 15) (j (l 15) (t (l 9) (t (l 9) (l 15))))) (j (t (j (t (l 15) (l 14)) (l 15)) (s (s (s (s (s (s (t (j (l 14) (l 15)) (l 14)) (l 14)) (l 14)) (l 14)) (l 14)) (l 14)) (l 14))) (l 15))) (s (t (j (l 15) (t (j (l 15) (l 9)) (s (t (j (l 15) (l 9)) (l 15)) (l 8)))) (t (l 8) (j (l 14) (l 15)))) (s (t (t (j (l 15) (t (l 9) (j (l 15) (l 9)))) (l 8)) (t (l 8) (j (l 14) (l 15)))) (s (s (t (t (t (j (l 15) (l 9)) (l 8)) (l 8)) (t (l 8) (j (l 14) (l 15)))) (s (t (t (t (j (l 15) (l 9)) (l 8)) (l 8)) (t (l 8) (j (l 14) (l 15)))) (s (t (t (t (j (l 15) (l 9)) (l 8)) (l 8)) (t (l 8) (j (l 14) (l 15)))) (s (t (t (t (j (l 15) (l 9)) (l 8)) (l 8)) (t (l 8) (j (l 14) (l 15)))) (t (t (t (j (l 15) (l 9)) (l 8)) (l 8)) (t (l 8) (j (l 14) (l 15)))))))) (s (s (s (s (t (t (t (j (l 15) (l 9)) (l 8)) (l 8)) (t (l 8) (j (l 14) (l 15)))) (t (t (t (j (l 15) (l 9)) (l 8)) (l 8)) (t (l 8) (j (l 14) (l 15))))) (t (t (t (j (l 15) (l 9)) (l 8)) (l 8)) (t (l 8) (j (l 14) (l 15))))) (t (t (t (j (l 15) (l 9)) (l 8)) (l 8)) (t (l 8) (j (l 14) (l 15))))) (t (t (t (j (l 15) (l 9)) (l 8)) (l 8)) (t (l 8) (j (l 14) (s (l 15) (t (l 15) (j (l 14) (l 15)))))))))))))) (t (s (s (s (s (s (s (s (s (s (s (t (t (t (t (t (t (t (t (t (j (l 15) (l 9)) (l 8)) (l 8)) (l 8)) (l 8)) (l 8)) (l 8)) (l 8)) (l 8)) (l 8)) (l 8)) (l 8)) (l 8)) (l 8)) (l 8)) (l 8)) (l 8)) (l 8)) (l 8)) (l 8)) (s (s (s (s (s (t (l 8) (t (l 8) (t (l 8) (t (l 8) (t (l 8) (s (j (l 14) (j (l 14) (l 15))) (q 8))))))) (l 8)) (l 8)) (l 8)) (l 8)) (q 8)))) (s (j (s (t (j (l 14) (t (s (l 15) (s (l 15) (l 14))) (s (j (l 14) (s (l 15) (l 14))) (l 14)))) (l 14)) (t (l 14) (q 14))) (s (t (l 15) (j (t (t (s (l 15) (s (l 19) (l 14))) (l 19)) (l 19)) (j (l 19) (l 15)))) (t (j (t (s (l 15) (s (t (l 15) (l 14)) (l 14))) (l 14)) (s (l 15) (t (l 15) (q 15)))) (q 15)))) (s (s (s (s (s (s (s (s (s (s (t (t (t (t (t (t (t (t (t (t (j (q 14) (j (q 14) (q 15))) (k)) (k)) (k)) (k)) (k)) (k)) (k)) (k)) (k)) (k)) (k)) (k)) (k)) (k)) (k)) (k)) (k)) (k)) (k)) (k))))) (s (t (s (t (s (j (j (l 17) (s (t (l 5) (l 18)) (l 18))) (l 18)) (j (l 18) (j (l 18) (s (s (l 18) (t (l 18) (l 19))) (s (j (l 18) (l 19)) (l 19)))))) (s (s (j (j (l 17) (l 18)) (l 18)) (s (l 18) (t (l 18) (t (l 18) (s (s (l 18) (l 16)) (l 16)))))) (j (s (l 18) (s (l 18) (t (l 18) (j (l 18) (t (l 18) (l 19)))))) (j (s (s (l 18) (j (l 18) (t (l 18) (l 19)))) (s (t (l 18) (l 19)) (l 19))) (l 19))))) (j (s (t (s (l 18) (s (l 18) (t (l 18) (j (l 18) (l 19))))) (j (s (l 18) (t (l 18) (q 18))) (s (t (s (l 18) (l 19)) (l 19)) (l 19)))) (t (s (s (t (s (l 18) (t (l 18) (j (l 18) (l 19)))) (j (l 18) (l 19))) (l 14)) (t (l 14) (q 14))) (q 19))) (s (s (t (j (j (t (l 18) (l 19)) (l 19)) (l 19)) (l 19)) (l 19)) (t (l 19) (q 19))))) (s (t (t (t (t (t (t (t (t (t (t (s (s (s (s (j (l 17) (l 18)) (l 16)) (l 16)) (l 16)) (s (l 16) (s (l 16) (s (l 16) (s (l 16) (s (s (l 16) (s (l 16) (s (l 16) (s (l 16) (j (j (l 18) (l 19)) (l 19)))))) (s (s (j (j (l 18) (l 19)) (l 19)) (s (j (j (l 18) (l 19)) (l 19)) (l 19))) (l 19)))))))) (s (s (s (s (j (l 17) (l 18)) (l 16)) (l 16)) (l 16)) (s (l 16) (s (l 16) (s (l 16) (s (l 16) (s (l 16) (s (s (j (j (l 18) (l 19)) (l 19)) (s (j (j (l 18) (l 19)) (l 19)) (l 19))) (l 19))))))))) (s (s (s (s (j (l 17) (l 18)) (l 16)) (l 16)) (l 16)) (s (l 16) (s (l 16) (s (l 16) (s (l 16) (s (l 16) (s (s (j (j (l 18) (l 19)) (l 19)) (s (s (t (j (j (l 18) (l 19)) (l 19)) (l 19)) (l 19)) (l 19))) (l 19))))))))) (s (s (s (s (j (l 17) (l 18)) (l 16)) (l 16)) (l 16)) (s (l 16) (s (l 16) (s (l 16) (s (l 16) (s (l 16) (s (s (l 16) (l 19)) (l 19))))))))) (s (l 16) (s (l 16) (s (l 16) (s (l 16) (s (l 16) (s (l 16) (s (l 16) (q 19))))))))) (l 16)) (l 16)) (l 16)) (l 16)) (l 16)) (s (l 16) (q 16))) (q 19))) (s (s (s (s (s (s (s (s (s (s (s (t (t (t (t (t (t (t (t (t (t (t (j (q 14) (q 19)) (k)) (k)) (k)) (k)) (k)) (k)) (k)) (k)) (k)) (k)) (k)) (k)) (k)) (k)) (k)) (k)) (k)) (k)) (k)) (k)) (k)) (k)))

open Tr in
def trpp2 : Tr := t (s (t (j (s (s (t (l 0) (t (s (l 0) (j (s (l 0) (l 5)) (s (l 0) (l 6)))) (s (l 6) (j (l 5) (l 6))))) (s (t (t (l 0) (s (l 0) (l 5))) (j (l 5) (j (l 5) (l 6)))) (l 5))) (t (l 5) (s (s (l 5) (s (l 5) (s (l 5) (l 9)))) (l 9)))) (t (s (s (l 0) (t (s (l 0) (s (s (l 0) (s (l 0) (t (l 0) (j (l 5) (l 6))))) (j (l 5) (t (l 5) (l 6))))) (t (s (l 0) (j (l 5) (l 6))) (l 6)))) (j (s (l 5) (s (l 5) (j (l 5) (s (j (l 5) (l 10)) (l 10))))) (s (l 6) (l 10)))) (s (s (s (t (l 0) (t (s (l 0) (l 6)) (s (j (l 6) (l 7)) (l 6)))) (l 6)) (l 6)) (s (s (l 6) (s (l 6) (s (l 6) (j (j (t (l 5) (l 9)) (l 6)) (l 6))))) (j (t (s (j (s (l 5) (l 9)) (s (l 6) (j (s (l 6) (l 9)) (l 6)))) (s (s (s (s (s (t (t (t (t (l 5) (l 9)) (l 9)) (l 9)) (l 9)) (l 9)) (l 9)) (l 9)) (l 9)) (l 9))) (s (s (j (l 9) (l 6)) (l 9)) (l 9))) (s (l 6) (t (l 10) (j (l 9) (t (l 10) (l 9)))))))))) (s (s (t (l 6) (j (s (l 6) (j (j (t (j (l 5) (l 6)) (l 18)) (l 6)) (l 6))) (j (l 6) (s (l 19) (t (l 6) (l 19)))))) (t (j (j (t (l 5) (t (l 5) (t (l 5) (j (l 5) (s (l 6) (l 19)))))) (s (l 6) (t (l 6) (l 19)))) (l 6)) (t (j (j (j (t (l 5) (s (t (l 5) (j (l 5) (j (l 5) (l 19)))) (l 19))) (s (s (l 6) (l 19)) (l 19))) (l 19)) (l 6)) (s (s (t (j (j (j (j (l 18) (l 19)) (l 19)) (l 19)) (l 19)) (l 19)) (l 19)) (j (l 19) (j (l 19) (j (s (l 19) (s (l 19) (l 20))) (l 20)))))))) (j (s (t (j (t (l 5) (t (s (l 5) (l 19)) (l 19))) (t (s (j (s (l 5) (l 9)) (s (l 6) (l 9))) (l 9)) (s (l 19) (s (l 19) (l 9))))) (l 19)) (j (t (t (j (t (s (l 5) (l 9)) (s (s (l 5) (l 19)) (l 15))) (l 9)) (s (l 19) (s (l 19) (l 15)))) (s (l 19) (l 15))) (t (l 9) (s (j (l 19) (t (l 9) (s (j (l 19) (l 20)) (l 20)))) (j (s (s (t (l 19) (l 15)) (l 15)) (l 15)) (t (s (l 9) (t (l 9) (l 20))) (l 20))))))) (s (t (s (l 6) (j (s (t (l 6) (l 9)) (l 9)) (s (l 6) (s (l 6) (t (l 6) (l 9)))))) (j (s (s (l 19) (j (l 19) (t (l 9) (l 20)))) (t (l 9) (t (l 9) (l 20)))) (s (t (t (l 6) (s (t (l 6) (l 20)) (l 20))) (l 20)) (l 20)))) (s (s (t (t (j (l 9) (l 6)) (l 9)) (t (l 9) (l 20))) (t (s (s (s (s (s (s (s (t (j (l 9) (l 6)) (l 9)) (l 9)) (l 9)) (l 9)) (l 9)) (l 9)) (l 9)) (l 9)) (t (l 9) (l 20)))) (t (l 9) (l 20))))))) (t (s (s (j (s (l 9) (s (l 9) (t (l 9) (t (l 9) (j (t (l 9) (l 15)) (l 9)))))) (t (t (l 10) (j (j (l 9) (l 10)) (l 10))) (t (j (l 9) (j (l 9) (l 10))) (l 9)))) (s (t (j (l 9) (j (t (l 10) (l 9)) (l 10))) (t (l 9) (j (j (l 15) (l 9)) (l 9)))) (s (t (j (l 9) (j (t (l 10) (l 9)) (s (l 10) (s (l 10) (t (l 10) (t (l 10) (l 9))))))) (j (j (t (t (l 9) (l 15)) (l 15)) (s (l 9) (t (l 9) (t (l 9) (l 15))))) (l 9))) (s (t (j (l 9) (t (s (l 10) (t (l 10) (j (l 9) (l 10)))) (s (t (j (l 9) (l 10)) (l 9)) (l 8)))) (t (l 8) (j (t (j (l 15) (l 9)) (l 15)) (l 9)))) (s (t (t (j (l 9) (t (l 10) (t (l 10) (l 8)))) (l 8)) (t (l 8) (j (t (l 8) (l 15)) (l 9)))) (s (s (t (t (t (j (l 9) (l 10)) (l 8)) (l 8)) (t (l 8) (j (l 15) (l 9)))) (s (t (t (t (j (l 9) (l 10)) (l 8)) (l 8)) (t (l 8) (j (l 15) (l 9)))) (s (t (t (t (j (l 9) (l 10)) (l 8)) (l 8)) (t (l 8) (j (l 15) (l 9)))) (s (t (t (t (j (l 9) (l 10)) (l 8)) (l 8)) (t (l 8) (j (l 15) (l 9)))) (t (t (t (j (l 9) (l 10)) (l 8)) (l 8)) (t (l 8) (j (l 15) (l 9)))))))) (s (s (s (s (t (t (t (j (l 9) (l 10)) (l 8)) (l 8)) (t (l 8) (j (l 15) (l 9)))) (t (t (t (j (l 9) (l 10)) (l 8)) (l 8)) (t (l 8) (j (l 15) (l 9))))) (t (t (t (j (l 9) (l 10)) (l 8)) (l 8)) (t (l 8) (j (l 15) (l 9))))) (t (t (t (j (l 9) (l 10)) (l 8)) (l 8)) (t (l 8) (j (l 15) (l 9))))) (t (t (t (j (l 9) (l 10)) (l 8)) (l 8)) (t (l 8) (j (l 15) (l 9))))))))))) (t (s (s (s (s (s (s (s (s (s (s (t (t (t (t (t (t (t (t (t (j (l 9) (l 10)) (l 8)) (l 8)) (l 8)) (l 8)) (l 8)) (l 8)) (l 8)) (l 8)) (l 8)) (l 8)) (l 8)) (l 8)) (l 8)) (l 8)) (l 8)) (l 8)) (l 8)) (l 8)) (l 8)) (s (s (s (s (s (t (l 8) (j (l 15) (l 9))) (l 8)) (l 8)) (l 8)) (l 8)) (q 8)))) (s (j (s (t (j (s (s (s (t (j (l 15) (l 9)) (l 15)) (l 15)) (l 15)) (l 15)) (t (l 9) (j (s (t (l 9) (l 15)) (l 15)) (s (l 9) (l 15))))) (l 15)) (t (s (s (s (s (s (s (s (t (j (l 15) (l 9)) (l 15)) (l 15)) (l 15)) (l 15)) (l 15)) (l 15)) (l 15)) (l 15)) (q 15))) (j (t (s (l 9) (t (s (l 9) (j (l 15) (l 9))) (s (s (l 9) (l 15)) (q 9)))) (s (l 20) (q 9))) (s (l 9) (t (l 9) (q 9))))) (s (s (s (s (s (s (s (s (s (s (t (t (t (t (t (t (t (t (t (t (j (q 15) (q 9)) (k)) (k)) (k)) (k)) (k)) (k)) (k)) (k)) (k)) (k)) (k)) (k)) (k)) (k)) (k)) (k)) (k)) (k)) (k)) (k))))) (s (t (s (t (s (j (j (s (l 18) (j (l 18) (l 19))) (l 19)) (l 19)) (j (l 19) (j (s (l 19) (s (l 19) (t (l 19) (l 20)))) (s (j (l 19) (l 20)) (l 20))))) (s (s (j (j (j (l 18) (l 19)) (l 19)) (l 19)) (s (l 19) (t (l 19) (t (l 19) (s (t (l 19) (l 16)) (l 16)))))) (j (s (l 19) (t (l 19) (t (s (l 19) (j (l 19) (l 20))) (j (l 19) (j (s (l 19) (l 20)) (l 20)))))) (s (j (j (s (l 19) (t (l 19) (l 20))) (t (l 19) (l 20))) (l 20)) (l 20))))) (j (j (t (s (l 19) (l 15)) (s (t (s (l 19) (j (l 19) (l 20))) (s (j (l 19) (l 20)) (q 19))) (q 19))) (t (s (s (l 19) (j (t (l 19) (l 20)) (s (t (l 19) (l 20)) (l 20)))) (s (s (s (s (t (j (l 19) (l 20)) (l 20)) (l 20)) (l 20)) (l 20)) (l 20))) (s (s (s (s (t (l 19) (l 20)) (l 20)) (l 20)) (l 20)) (q 20)))) (s (s (s (s (t (t (j (l 19) (l 20)) (l 20)) (l 20)) (l 20)) (l 20)) (l 20)) (t (l 20) (q 20))))) (s (t (t (t (t (t (t (t (t (t (t (s (s (s (s (s (j (j (l 18) (l 19)) (l 19)) (l 16)) (l 16)) (l 16)) (l 16)) (s (l 16) (s (l 16) (s (l 16) (s (l 16) (l 20)))))) (s (s (s (s (s (s (j (j (l 18) (l 19)) (l 19)) (l 16)) (l 16)) (l 16)) (l 16)) (l 16)) (s (l 16) (s (l 16) (s (l 16) (s (l 16) (l 20))))))) (s (s (s (s (s (s (j (j (l 18) (l 19)) (l 19)) (l 16)) (l 16)) (l 16)) (l 16)) (l 16)) (s (l 16) (s (l 16) (s (l 16) (s (l 16) (l 20))))))) (s (s (s (s (s (s (s (j (j (l 18) (l 19)) (l 19)) (l 16)) (l 16)) (l 16)) (l 16)) (l 16)) (l 16)) (s (l 16) (s (l 16) (s (l 16) (s (l 16) (l 20))))))) (s (l 16) (s (l 16) (s (l 16) (s (l 16) (s (l 16) (l 20))))))) (l 16)) (l 16)) (l 16)) (l 16)) (l 16)) (s (l 16) (q 16))) (q 20))) (s (s (s (s (s (s (s (s (s (s (s (t (t (t (t (t (t (t (t (t (t (t (j (q 15) (q 20)) (k)) (k)) (k)) (k)) (k)) (k)) (k)) (k)) (k)) (k)) (k)) (k)) (k)) (k)) (k)) (k)) (k)) (k)) (k)) (k)) (k)) (k)))

open Tr in
def trpp3 : Tr := s (t (s (t (s (t (l 0) (t (t (l 0) (t (s (l 0) (s (l 0) (j (s (l 0) (l 6)) (l 7)))) (s (l 0) (s (l 0) (j (j (l 6) (l 7)) (l 7)))))) (s (l 7) (s (l 7) (s (l 7) (s (l 7) (j (t (l 6) (l 7)) (l 7)))))))) (t (s (s (l 0) (s (t (l 0) (t (l 0) (j (l 6) (l 7)))) (s (t (l 0) (t (l 0) (j (l 6) (l 7)))) (l 6)))) (l 6)) (j (l 6) (l 7)))) (s (s (l 7) (s (l 7) (t (l 7) (t (l 7) (t (s (l 7) (t (l 7) (s (t (l 7) (l 20)) (l 20)))) (s (t (s (l 7) (s (l 7) (l 20))) (l 20)) (l 20))))))) (t (j (j (s (s (l 7) (l 6)) (l 6)) (s (l 7) (t (l 7) (s (l 7) (l 20))))) (l 7)) (j (j (t (j (s (t (l 6) (j (l 6) (t (l 6) (l 20)))) (t (l 6) (l 20))) (s (s (l 7) (l 20)) (l 20))) (s (s (s (s (s (j (j (l 19) (l 20)) (l 20)) (l 20)) (l 20)) (l 20)) (l 20)) (l 20))) (l 20)) (l 20))))) (t (t (s (l 6) (s (l 6) (s (l 6) (t (l 6) (t (l 6) (l 10)))))) (s (j (l 6) (j (j (l 6) (t (l 6) (s (l 7) (s (l 7) (l 10))))) (l 7))) (s (t (t (s (l 6) (t (l 6) (l 10))) (s (s (t (t (l 6) (s (t (l 6) (l 10)) (l 10))) (l 10)) (l 10)) (l 10))) (l 10)) (l 10)))) (j (t (j (s (t (l 6) (s (t (l 6) (l 20)) (l 20))) (t (t (l 10) (j (s (l 20) (l 9)) (l 10))) (s (l 20) (l 9)))) (s (t (t (s (l 6) (l 10)) (s (t (l 6) (l 20)) (l 10))) (l 20)) (s (l 10) (s (l 10) (s (l 10) (t (l 10) (t (l 10) (l 9)))))))) (s (l 20) (s (s (l 20) (s (l 20) (t (l 20) (l 9)))) (s (t (s (t (j (l 9) (j (l 20) (l 10))) (l 9)) (s (s (t (t (t (j (l 9) (j (l 9) (l 10))) (l 9)) (l 9)) (l 9)) (l 9)) (l 9))) (l 9)) (l 9))))) (s (s (t (s (l 7) (t (l 7) (l 10))) (s (l 20) (s (l 20) (j (l 20) (t (l 10) (l 20)))))) (t (l 10) (j (s (l 20) (s (l 20) (s (l 20) (t (l 10) (t (l 20) (l 21)))))) (l 10)))) (t (l 10) (t (l 10) (s (t (t (l 10) (l 21)) (l 21)) (l 21)))))))) (s (t (s (j (s (j (s (l 19) (t (l 19) (l 20))) (s (j (l 19) (l 20)) (l 20))) (s (t (j (l 19) (l 20)) (l 20)) (l 20))) (l 20)) (t (l 20) (t (s (l 20) (j (l 20) (j (l 20) (l 21)))) (j (s (l 20) (s (l 20) (j (l 20) (s (l 20) (l 21))))) (s (t (l 20) (s (l 16) (s (l 16) (l 21)))) (l 21)))))) (t (t (t (t (t (t (t (t (t (t (s (s (s (s (j (l 19) (l 20)) (l 16)) (l 16)) (l 20)) (s (l 16) (s (l 16) (s (l 16) (l 21))))) (s (s (s (s (j (l 19) (l 20)) (l 16)) (l 16)) (l 20)) (s (l 16) (s (l 16) (s (l 16) (l 21)))))) (s (s (s (s (j (l 19) (l 20)) (l 16)) (l 16)) (l 20)) (s (l 16) (s (l 16) (s (l 16) (l 21)))))) (s (s (s (s (j (l 19) (l 20)) (l 16)) (l 16)) (l 16)) (s (l 16) (s (l 16) (s (l 16) (l 21)))))) (s (l 16) (s (l 16) (s (l 16) (s (l 16) (l 21)))))) (l 16)) (l 16)) (l 16)) (l 16)) (l 16)) (s (l 16) (q 16)))) (t (j (s (t (s (l 20) (s (l 20) (s (l 20) (t (l 20) (j (l 20) (l 21)))))) (j (t (s (l 20) (s (l 20) (l 21))) (s (s (l 20) (l 21)) (q 20))) (s (t (s (l 20) (l 21)) (l 21)) (l 21)))) (t (s (s (t (s (l 20) (s (l 20) (l 9))) (j (l 20) (l 21))) (l 9)) (l 9)) (q 21))) (s (s (t (j (t (l 20) (s (l 20) (l 21))) (l 21)) (l 21)) (l 21)) (l 21))) (q 21)))) (t (t (s (s (t (t (j (l 10) (s (l 6) (t (l 11) (l 10)))) (l 10)) (s (l 10) (s (l 10) (s (l 10) (t (l 10) (t (l 10) (j (t (l 10) (l 9)) (l 10)))))))) (t (t (t (j (l 10) (t (l 11) (l 10))) (l 10)) (l 10)) (s (t (l 10) (j (j (l 9) (l 10)) (l 10))) (j (t (j (s (t (l 10) (l 9)) (l 8)) (l 10)) (l 9)) (s (l 10) (s (l 10) (s (l 10) (t (l 10) (t (l 10) (t (l 10) (l 9))))))))))) (t (s (s (s (s (s (s (s (s (s (s (t (t (t (t (t (t (t (t (t (j (l 10) (l 11)) (l 8)) (l 8)) (l 8)) (l 8)) (l 8)) (l 8)) (l 8)) (l 8)) (l 8)) (l 8)) (l 8)) (l 8)) (l 8)) (l 8)) (l 8)) (l 8)) (l 8)) (l 8)) (l 8)) (s (s (s (s (s (t (l 8) (t (l 8) (t (l 8) (l 9)))) (l 8)) (l 8)) (l 8)) (l 8)) (q 8)))) (s (j (s (t (j (l 9) (t (s (l 10) (s (l 10) (l 9))) (s (t (l 10) (l 9)) (l 9)))) (l 9)) (t (l 9) (q 9))) (t (s (s (l 10) (s (l 10) (s (l 10) (s (l 10) (t (l 10) (t (l 10) (l 9))))))) (t (s (l 10) (j (l 9) (s (l 10) (l 9)))) (s (j (l 9) (s (l 10) (l 9))) (q 9)))) (s (t (t (s (l 10) (j (l 9) (l 10))) (l 21)) (l 21)) (q 9)))) (q 9))) (s (s (s (s (s (s (s (s (s (s (s (t (t (t (t (t (t (t (t (t (t (t (j (q 9) (q 21)) (k)) (k)) (k)) (k)) (k)) (k)) (k)) (k)) (k)) (k)) (k)) (k)) (k)) (k)) (k)) (k)) (k)) (k)) (k)) (k)) (k)) (k)))

open Tr in
def trpm0 : Tr := t (s (t (s (s (t (l 0) (s (t (l 0) (t (s (l 0) (j (l 7) (l 1))) (j (j (l 7) (l 1)) (l 1)))) (j (s (t (l 0) (l 7)) (l 7)) (t (t (l 0) (j (s (l 0) (l 7)) (l 1))) (l 1))))) (t (t (s (l 0) (t (j (s (l 0) (j (l 6) (l 7))) (l 7)) (l 7))) (s (s (l 0) (l 7)) (l 7))) (s (s (s (t (l 7) (j (l 7) (t (l 7) (l 1)))) (l 7)) (l 7)) (l 7)))) (s (t (t (t (j (l 6) (l 7)) (l 7)) (l 7)) (l 7)) (s (t (j (t (t (l 6) (l 11)) (l 7)) (l 7)) (j (l 7) (l 11))) (t (j (l 11) (l 7)) (j (j (t (t (l 11) (j (l 10) (l 11))) (l 10)) (s (l 7) (t (l 11) (t (l 11) (l 10))))) (l 11)))))) (s (j (t (s (s (s (l 1) (l 7)) (l 7)) (l 7)) (s (t (s (j (l 7) (l 1)) (l 7)) (l 20)) (t (s (l 7) (s (l 7) (s (l 7) (s (l 7) (s (l 7) (s (l 7) (s (l 7) (t (l 7) (j (l 7) (l 21)))))))))) (j (l 20) (s (s (l 20) (j (l 20) (l 21))) (l 21)))))) (s (s (l 1) (s (l 1) (t (l 1) (t (l 1) (t (l 1) (l 21)))))) (t (j (s (s (l 1) (l 7)) (l 7)) (s (l 1) (t (l 1) (s (l 1) (l 21))))) (s (t (s (s (l 1) (t (l 1) (s (t (l 1) (l 21)) (l 21)))) (t (j (j (l 7) (l 21)) (l 21)) (l 21))) (l 21)) (l 21))))) (j (s (t (s (l 7) (s (l 7) (s (l 7) (t (l 7) (t (l 7) (l 10)))))) (j (s (t (s (l 7) (s (l 7) (l 10))) (l 21)) (l 10)) (s (s (s (s (s (t (t (l 7) (l 21)) (l 21)) (l 21)) (l 21)) (l 21)) (l 21)) (l 21)))) (s (t (t (j (l 10) (s (l 7) (s (l 7) (l 10)))) (l 10)) (l 10)) (l 10))) (s (t (t (j (l 7) (t (s (l 7) (l 11)) (s (j (l 7) (l 21)) (l 11)))) (s (s (j (t (l 7) (l 21)) (l 21)) (l 21)) (l 21))) (l 21)) (j (t (t (t (l 11) (j (s (l 21) (l 10)) (l 11))) (s (l 21) (l 10))) (s (l 21) (l 10))) (t (s (l 11) (s (l 11) (s (l 11) (s (l 11) (s (l 11) (s (l 11) (t (l 11) (t (l 11) (l 10))))))))) (s (s (l 21) (j (l 21) (j (l 21) (t (l 11) (l 22))))) (s (t (j (l 10) (t (l 11) (j (l 10) (l 11)))) (l 10)) (l 10))))))))) (t (s (t (s (l 11) (s (l 11) (t (l 11) (s (t (l 11) (j (l 10) (l 11))) (t (s (l 11) (l 8)) (l 8)))))) (j (s (t (j (l 10) (l 11)) (l 10)) (l 10)) (s (l 11) (t (s (l 11) (s (s (l 11) (s (l 11) (s (s (l 11) (t (l 11) (j (l 10) (l 11)))) (t (l 11) (j (l 10) (l 11)))))) (l 8))) (j (l 10) (s (l 11) (s (t (l 11) (l 10)) (l 10)))))))) (t (s (s (s (s (s (s (s (s (s (s (t (l 11) (l 8)) (l 8)) (l 8)) (l 8)) (l 8)) (l 8)) (l 8)) (l 8)) (l 8)) (l 8)) (l 8)) (s (s (s (t (l 8) (l 10)) (l 8)) (l 8)) (q 8)))) (s (s (t (j (l 10) (j (l 10) (t (s (l 11) (s (l 11) (l 10))) (s (t (l 11) (l 10)) (l 10))))) (s (l 10) (t (l 10) (q 10)))) (t (s (l 10) (t (l 10) (q 10))) (q 10))) (q 10)))) (s (t (s (s (j (s (l 20) (s (l 20) (t (l 20) (j (l 20) (l 21))))) (s (j (s (l 20) (t (l 20) (l 21))) (s (j (s (l 20) (l 21)) (l 21)) (l 21))) (s (s (t (j (l 20) (l 21)) (l 21)) (l 21)) (l 21)))) (s (t (j (j (l 20) (s (l 20) (l 21))) (l 21)) (l 21)) (s (l 21) (t (l 21) (t (l 21) (t (l 21) (t (s (l 21) (s (l 21) (s (l 21) (j (l 21) (l 22))))) (j (l 21) (j (l 21) (l 22)))))))))) (j (s (s (l 21) (s (l 21) (s (l 21) (s (l 21) (t (l 21) (t (l 21) (k))))))) (t (s (l 21) (t (l 21) (q 21))) (q 21))) (s (t (s (l 21) (s (l 21) (t (l 21) (j (l 21) (l 22))))) (j (t (s (l 21) (s (l 21) (l 22))) (s (s (l 21) (l 22)) (q 21))) (s (s (t (l 21) (l 22)) (l 22)) (l 22)))) (t (j (l 10) (j (l 10) (l 22))) (q 22))))) (s (t (t (t (t (t (t (t (t (t (t (s (s (s (s (l 20) (l 16)) (l 16)) (l 16)) (s (l 21) (s (l 16) (s (l 16) (j (l 21) (l 22)))))) (s (s (s (s (l 20) (l 16)) (l 16)) (l 16)) (s (l 21) (s (l 16) (s (l 16) (j (l 21) (l 22))))))) (s (s (s (s (l 20) (l 16)) (l 16)) (l 16)) (s (l 21) (s (l 16) (s (l 16) (j (l 21) (l 22))))))) (s (s (s (s (l 20) (l 16)) (l 16)) (l 16)) (s (l 21) (s (l 16) (s (l 16) (j (l 21) (l 22))))))) (s (l 16) (s (l 16) (s (l 16) (s (l 16) (j (l 21) (l 22))))))) (l 16)) (l 16)) (l 16)) (l 16)) (l 16)) (s (l 16) (q 16))) (s (s (s (s (s (s (s (s (s (s (t (t (t (t (t (t (t (t (t (t (j (q 21) (q 22)) (k)) (k)) (k)) (k)) (k)) (k)) (k)) (k)) (k)) (k)) (k)) (k)) (k)) (k)) (k)) (k)) (k)) (k)) (k)) (k)))) (q 10))

open Tr in
def trpm1 : Tr := t (s (t (t (s (s (l 0) (t (s (l 0) (j (s (s (l 0) (s (l 0) (l 7))) (l 7)) (s (s (l 0) (l 1)) (l 1)))) (t (s (l 0) (j (j (l 7) (l 1)) (l 1))) (l 1)))) (j (j (l 7) (s (t (l 7) (l 1)) (s (j (s (l 7) (j (l 7) (l 12))) (l 12)) (l 12)))) (l 1))) (s (s (s (t (l 0) (j (t (s (l 0) (l 1)) (l 1)) (l 2))) (j (l 1) (j (s (t (l 0) (l 1)) (l 1)) (t (t (l 0) (l 2)) (l 2))))) (s (s (t (l 1) (j (l 1) (j (l 1) (l 2)))) (l 1)) (l 1))) (s (j (j (j (t (l 7) (s (l 1) (l 11))) (l 1)) (l 1)) (l 1)) (j (j (s (s (t (t (l 7) (l 11)) (l 11)) (l 11)) (l 11)) (s (s (l 1) (s (l 1) (t (s (l 1) (s (l 1) (s (l 1) (j (j (l 11) (l 1)) (l 1))))) (j (l 11) (l 1))))) (t (j (j (l 11) (t (l 12) (l 11))) (l 12)) (l 11)))) (s (j (l 1) (l 12)) (l 12)))))) (s (j (t (l 1) (t (l 1) (s (l 21) (s (l 21) (s (l 21) (j (l 21) (j (l 21) (l 22)))))))) (j (s (s (l 2) (t (t (l 1) (l 2)) (j (t (s (l 2) (l 1)) (l 21)) (s (l 2) (s (l 2) (t (l 2) (l 22))))))) (t (l 1) (t (j (s (l 1) (t (l 1) (s (l 1) (l 22)))) (t (s (j (l 1) (l 2)) (l 22)) (s (s (s (l 2) (l 22)) (l 22)) (l 22)))) (s (j (s (l 21) (j (l 21) (l 22))) (l 22)) (l 22))))) (s (l 2) (t (s (l 2) (t (j (l 1) (l 2)) (s (l 2) (l 22)))) (l 22))))) (j (s (t (j (s (s (l 1) (t (l 1) (l 11))) (l 11)) (s (l 1) (s (l 1) (t (l 1) (l 11))))) (j (j (l 21) (s (l 21) (t (l 11) (t (l 11) (l 22))))) (j (s (s (t (l 1) (l 21)) (l 11)) (l 11)) (s (t (t (l 1) (l 22)) (l 22)) (l 22))))) (t (s (s (s (s (s (s (t (j (l 11) (l 1)) (l 11)) (l 11)) (l 11)) (l 11)) (l 11)) (l 11)) (l 11)) (t (l 11) (l 22)))) (s (t (j (t (l 1) (s (j (l 1) (s (l 1) (l 22))) (s (t (l 1) (l 22)) (l 22)))) (t (j (s (l 1) (l 12)) (s (s (l 2) (l 12)) (l 12))) (l 22))) (l 22)) (j (t (t (t (s (l 1) (j (l 11) (l 12))) (j (j (l 11) (l 22)) (s (l 22) (l 12)))) (l 22)) (l 22)) (t (t (l 12) (t (l 12) (t (l 12) (j (s (l 22) (s (l 22) (l 11))) (l 12))))) (s (j (l 22) (s (s (l 22) (s (l 22) (s (l 22) (s (l 22) (s (l 22) (t (l 22) (t (l 22) (l 23)))))))) (t (j (l 22) (l 12)) (j (s (l 22) (l 11)) (l 23))))) (j (l 11) (t (j (t (l 12) (l 11)) (l 12)) (l 23)))))))))) (t (s (j (t (j (t (j (t (l 12) (l 11)) (s (l 12) (l 11))) (l 11)) (s (l 12) (t (l 12) (s (t (l 12) (l 11)) (s (l 11) (s (l 11) (l 8))))))) (s (s (s (s (t (t (j (l 11) (l 12)) (l 11)) (l 11)) (l 11)) (l 11)) (l 11)) (l 11))) (t (l 12) (s (s (l 12) (t (l 12) (j (t (l 12) (l 11)) (l 12)))) (j (t (s (t (l 12) (l 11)) (s (t (l 12) (l 11)) (l 11))) (l 11)) (s (l 12) (t (l 12) (s (t (l 12) (l 11)) (l 11)))))))) (t (s (s (s (s (s (s (s (s (s (s (t (t (l 12) (l 8)) (l 8)) (l 8)) (l 8)) (l 8)) (l 8)) (l 8)) (l 8)) (l 8)) (l 8)) (l 8)) (l 8)) (s (s (s (s (s (t (l 8) (s (s (l 11) (s (s (l 11) (t (l 11) (t (l 11) (t (l 11) (t (l 11) (t (l 11) (k))))))) (t (l 11) (t (l 11) (t (l 11) (t (l 8) (t (l 8) (k)))))))) (s (s (s (s (t (l 11) (t (l 11) (t (l 8) (t (l 8) (q 8))))) (l 8)) (l 8)) (l 8)) (l 8)))) (l 8)) (l 8)) (l 8)) (l 8)) (q 8)))) (s (j (s (t (l 11) (s (s (t (l 11) (l 22)) (l 22)) (t (j (l 10) (l 11)) (q 22)))) (t (j (s (t (l 11) (l 10)) (l 10)) (s (l 11) (t (l 11) (q 11)))) (q 11))) (s (t (j (l 11) (t (s (l 12) (j (l 11) (l 12))) (j (l 11) (s (l 12) (l 11))))) (l 11)) (t (l 11) (q 11)))) (q 11)))) (s (t (t (s (j (s (l 21) (s (l 21) (j (l 21) (j (s (l 21) (l 22)) (l 22))))) (s (j (s (l 21) (j (l 21) (l 22))) (s (t (l 2) (l 22)) (l 22))) (l 22))) (s (s (t (j (j (j (l 21) (l 22)) (l 22)) (l 22)) (l 22)) (t (l 22) (j (l 22) (j (l 22) (j (l 22) (l 23)))))) (j (l 22) (j (t (l 11) (s (s (l 22) (l 11)) (q 11))) (j (l 11) (l 23)))))) (s (j (s (s (l 21) (s (l 21) (s (l 21) (t (l 21) (t (l 21) (l 16)))))) (j (s (s (l 21) (j (l 21) (t (l 21) (l 22)))) (s (t (l 21) (l 22)) (l 22))) (s (s (t (l 21) (l 22)) (l 22)) (l 22)))) (s (s (j (l 21) (l 22)) (l 22)) (s (l 22) (t (l 22) (t (l 22) (j (l 22) (j (l 22) (l 23)))))))) (s (j (l 22) (j (t (l 22) (s (s (l 22) (t (l 22) (q 22))) (q 22))) (s (s (t (l 22) (l 23)) (l 23)) (l 23)))) (s (s (s (s (s (s (s (s (s (t (t (t (t (t (t (t (t (t (j (q 22) (q 23)) (k)) (k)) (k)) (k)) (k)) (k)) (k)) (k)) (k)) (k)) (k)) (k)) (k)) (k)) (k)) (k)) (k)) (k))))) (s (t (t (t (t (t (t (t (t (t (t (s (s (s (s (s (l 21) (l 16)) (l 16)) (l 16)) (l 16)) (s (l 16) (s (l 16) (s (l 16) (s (l 16) (j (l 22) (j (l 22) (l 23)))))))) (s (s (s (s (s (l 21) (l 16)) (l 16)) (l 16)) (l 16)) (s (l 16) (s (l 16) (s (l 16) (s (l 16) (s (l 16) (j (l 22) (j (l 22) (l 23)))))))))) (s (s (s (s (s (l 21) (l 16)) (l 16)) (l 16)) (l 16)) (s (l 16) (s (l 16) (s (l 16) (s (l 16) (s (l 16) (j (l 22) (j (l 22) (l 23)))))))))) (s (s (s (s (s (l 21) (l 16)) (l 16)) (l 16)) (l 16)) (s (l 16) (s (l 16) (s (l 16) (s (l 16) (s (l 16) (j (l 22) (j (l 22) (l 23)))))))))) (s (l 16) (s (l 16) (s (l 16) (s (l 16) (s (l 16) (s (l 16) (s (l 16) (q 16))))))))) (l 16)) (l 16)) (l 16)) (l 16)) (l 16)) (s (l 16) (q 16))) (s (s (s (s (s (s (s (s (s (s (t (t (t (t (t (t (t (t (t (t (j (q 22) (j (q 22) (q 23))) (k)) (k)) (k)) (k)) (k)) (k)) (k)) (k)) (k)) (k)) (k)) (k)) (k)) (k)) (k)) (k)) (k)) (k)) (k)) (k)))) (s (s (s (s (s (s (s (s (s (s (s (t (t (t (t (t (t (t (t (t (t (t (j (q 22) (q 11)) (k)) (k)) (k)) (k)) (k)) (k)) (k)) (k)) (k)) (k)) (k)) (k)) (k)) (k)) (k)) (k)) (k)) (k)) (k)) (k)) (k)) (k)))

open Tr in
def trpm2 : Tr := t (s (t (t (s (s (l 0) (t (s (l 0) (j (s (s (l 0) (s (l 0) (t (l 0) (j (l 1) (l 2))))) (t (l 1) (j (l 1) (l 2)))) (l 2))) (t (s (l 0) (t (j (j (l 1) (l 2)) (l 2)) (l 2))) (l 2)))) (j (j (s (l 1) (s (l 1) (j (l 1) (j (l 1) (l 13))))) (s (t (t (l 1) (l 2)) (l 2)) (s (t (l 13) (l 2)) (l 13)))) (l 2))) (s (s (j (s (t (l 0) (t (s (l 0) (l 2)) (s (j (l 2) (l 3)) (l 2)))) (l 2)) (t (t (l 0) (t (s (l 0) (s (l 0) (j (l 2) (l 3)))) (s (l 0) (j (s (l 3) (l 2)) (l 3))))) (s (l 3) (s (l 3) (j (l 2) (l 3)))))) (s (j (l 2) (j (l 2) (j (l 2) (l 3)))) (l 2))) (s (s (l 2) (j (j (j (t (l 1) (s (l 2) (l 12))) (l 2)) (l 2)) (l 2))) (j (j (s (j (s (t (l 1) (l 12)) (l 12)) (s (t (s (l 2) (s (l 2) (s (l 2) (s (l 2) (j (l 12) (l 2)))))) (l 12)) (j (l 12) (t (l 2) (l 12))))) (l 12)) (s (l 2) (t (s (s (l 2) (s (l 2) (s (s (l 2) (t (l 13) (j (l 12) (l 13)))) (l 13)))) (l 13)) (j (l 12) (s (l 2) (t (l 13) (l 12))))))) (l 13))))) (s (j (t (s (s (s (j (l 2) (l 3)) (l 2)) (l 2)) (l 2)) (t (s (t (s (j (l 2) (s (l 3) (l 2))) (l 2)) (l 22)) (l 2)) (s (l 22) (j (l 22) (s (s (l 22) (s (l 22) (j (l 22) (s (l 22) (l 23))))) (j (t (l 2) (l 22)) (l 23))))))) (s (s (l 3) (s (l 3) (t (l 3) (t (l 3) (t (s (l 3) (t (l 3) (s (l 3) (l 23)))) (s (t (s (l 3) (l 23)) (l 23)) (l 23))))))) (t (j (t (l 2) (t (l 2) (j (l 2) (s (l 3) (l 23))))) (s (l 3) (t (l 3) (l 23)))) (s (t (s (j (j (j (l 2) (l 3)) (l 3)) (l 3)) (t (j (j (l 2) (l 23)) (l 23)) (l 23))) (l 23)) (l 23))))) (j (s (t (s (s (l 2) (s (l 2) (s (l 2) (s (l 2) (s (l 2) (s (l 2) (s (l 2) (t (l 2) (j (l 12) (l 2)))))))))) (j (s (j (l 12) (l 2)) (l 12)) (s (l 2) (s (l 2) (t (l 2) (t (l 2) (l 12))))))) (j (s (s (l 22) (j (l 22) (j (l 22) (l 12)))) (j (j (l 22) (s (l 22) (l 12))) (l 12))) (s (t (j (s (l 2) (s (l 2) (l 12))) (l 23)) (l 23)) (l 23)))) (s (s (t (t (j (l 12) (l 2)) (l 12)) (t (l 12) (l 23))) (t (s (s (t (j (l 12) (t (l 2) (l 12))) (l 12)) (l 12)) (l 12)) (t (l 12) (l 23)))) (t (l 12) (t (l 12) (l 23))))) (s (t (t (j (l 2) (s (j (s (l 2) (l 13)) (s (l 3) (l 13))) (l 13))) (t (t (j (s (l 2) (l 23)) (s (l 23) (l 13))) (l 23)) (l 23))) (l 23)) (j (s (t (t (t (l 13) (l 23)) (l 23)) (l 23)) (t (t (t (l 13) (j (l 12) (l 13))) (s (l 23) (l 12))) (l 12))) (t (l 13) (s (j (s (l 23) (s (l 23) (t (l 23) (l 12)))) (t (l 13) (s (j (l 23) (l 17)) (l 17)))) (j (s (s (t (t (j (l 23) (l 13)) (l 12)) (l 12)) (l 12)) (l 12)) (t (s (l 13) (t (l 13) (l 17))) (l 17)))))))))) (t (s (j (t (j (t (t (l 13) (j (l 12) (l 13))) (s (j (l 12) (l 13)) (l 12))) (s (l 13) (s (l 13) (t (l 13) (t (l 13) (l 12)))))) (s (t (j (l 12) (j (l 12) (l 13))) (l 12)) (l 12))) (t (l 13) (s (s (l 13) (s (l 13) (s (l 13) (s (l 13) (t (l 13) (j (l 12) (l 13))))))) (s (t (l 13) (j (l 12) (l 13))) (t (s (s (l 13) (s (t (l 13) (j (l 12) (l 13))) (t (l 13) (j (l 12) (l 13))))) (l 8)) (t (j (l 12) (j (l 12) (l 13))) (l 12))))))) (t (s (s (s (s (s (s (s (s (s (s (t (t (l 13) (l 8)) (l 8)) (l 8)) (l 8)) (l 8)) (l 8)) (l 8)) (l 8)) (l 8)) (l 8)) (l 8)) (l 8)) (s (s (s (s (s (t (l 8) (l 12)) (l 8)) (l 8)) (l 8)) (l 8)) (q 8)))) (s (j (j (t (s (l 12) (t (s (l 12) (j (l 11) (l 12))) (s (j (l 11) (l 12)) (q 11)))) (s (l 23) (q 11))) (t (s (l 12) (s (l 12) (t (l 12) (q 12)))) (s (s (l 12) (t (l 12) (q 12))) (q 12)))) (s (t (j (s (s (t (t (l 13) (l 12)) (l 12)) (l 12)) (l 12)) (t (l 13) (s (j (s (l 13) (l 12)) (l 13)) (l 12)))) (l 12)) (t (l 12) (q 12)))) (q 12)))) (s (t (t (s (j (s (l 22) (j (l 22) (s (j (l 22) (l 23)) (l 23)))) (s (j (s (l 22) (j (l 22) (l 23))) (l 23)) (l 23))) (j (s (s (t (j (j (l 22) (l 23)) (l 23)) (l 23)) (l 23)) (l 23)) (s (s (l 23) (j (l 23) (t (j (l 23) (s (l 23) (l 17))) (l 17)))) (j (l 12) (l 17))))) (s (j (s (s (l 22) (s (l 22) (j (l 22) (t (l 22) (l 23))))) (j (s (t (l 22) (j (t (l 22) (s (l 22) (l 23))) (s (s (l 22) (l 23)) (l 23)))) (s (s (t (l 22) (l 23)) (l 23)) (l 23))) (l 23))) (s (s (j (s (l 22) (l 23)) (l 23)) (l 23)) (s (l 23) (t (l 23) (j (l 23) (j (s (l 23) (l 17)) (l 17))))))) (s (j (s (l 23) (t (l 23) (q 23))) (j (t (s (l 23) (s (l 23) (l 17))) (s (j (l 23) (l 17)) (q 17))) (l 17))) (s (s (s (s (s (s (s (s (s (t (t (t (t (t (t (t (t (t (j (q 23) (q 17)) (k)) (k)) (k)) (k)) (k)) (k)) (k)) (k)) (k)) (k)) (k)) (k)) (k)) (k)) (k)) (k)) (k)) (k))))) (s (t (t (t (t (t (t (t (t (t (t (s (s (s (s (s (s (s (l 22) (j (l 22) (j (l 22) (l 23)))) (s (s (s (s (j (l 22) (j (l 22) (l 23))) (l 16)) (l 16)) (l 16)) (l 16))) (l 16)) (l 16)) (l 16)) (l 16)) (s (l 16) (s (l 16) (s (l 16) (j (l 23) (l 17)))))) (s (s (s (s (s (s (s (l 22) (j (l 22) (j (l 22) (l 23)))) (l 16)) (l 16)) (l 16)) (l 16)) (l 16)) (s (l 16) (s (l 16) (s (l 16) (j (l 23) (l 17))))))) (s (s (s (s (s (s (s (l 22) (j (l 22) (j (l 22) (l 23)))) (l 16)) (l 16)) (l 16)) (l 16)) (l 16)) (s (l 16) (s (l 16) (s (l 16) (j (l 23) (l 17))))))) (s (s (s (s (s (s (s (s (l 22) (t (l 22) (l 16))) (l 16)) (l 16)) (l 16)) (l 16)) (l 16)) (l 16)) (s (l 16) (s (l 16) (s (l 16) (j (l 23) (l 17))))))) (s (l 16) (s (l 16) (s (l 16) (s (l 16) (j (l 23) (l 17))))))) (l 16)) (l 16)) (l 16)) (l 16)) (l 16)) (s (l 16) (q 16))) (s (s (s (s (s (s (s (s (s (s (t (t (t (t (t (t (t (t (t (t (j (q 23) (q 17)) (k)) (k)) (k)) (k)) (k)) (k)) (k)) (k)) (k)) (k)) (k)) (k)) (k)) (k)) (k)) (k)) (k)) (k)) (k)) (k)))) (s (s (s (s (s (s (s (s (s (s (s (t (t (t (t (t (t (t (t (t (t (t (j (q 23) (q 12)) (k)) (k)) (k)) (k)) (k)) (k)) (k)) (k)) (k)) (k)) (k)) (k)) (k)) (k)) (k)) (k)) (k)) (k)) (k)) (k)) (k)) (k)))

open Tr in
def trpm3 : Tr := s (t (s (s (t (t (l 0) (s (t (l 0) (j (t (s (l 0) (l 3)) (l 3)) (l 4))) (s (t (l 0) (l 3)) (l 3)))) (j (s (t (l 3) (t (l 3) (l 23))) (l 3)) (s (l 4) (j (t (l 3) (t (s (l 4) (l 3)) (l 23))) (s (l 4) (s (l 4) (s (l 4) (t (l 4) (t (l 4) (l 17)))))))))) (t (t (t (s (l 0) (j (s (s (l 0) (l 2)) (l 2)) (s (s (l 0) (l 3)) (l 3)))) (t (s (l 0) (t (t (j (j (l 2) (l 3)) (l 3)) (l 3)) (l 3))) (l 3))) (l 3)) (t (s (s (s (s (s (s (t (l 3) (t (l 3) (t (l 3) (t (l 3) (t (l 3) (t (l 3) (t (l 3) (j (l 3) (j (l 3) (l 4)))))))))) (l 3)) (l 3)) (l 3)) (l 3)) (l 3)) (l 3)) (j (t (l 3) (s (l 23) (s (l 23) (s (l 23) (j (l 23) (j (l 23) (l 17))))))) (t (j (s (l 3) (j (l 3) (s (l 3) (l 17)))) (t (j (s (l 3) (l 17)) (s (l 4) (l 17))) (s (s (l 4) (l 17)) (l 17)))) (s (j (j (l 23) (s (s (l 23) (l 17)) (l 17))) (l 17)) (l 17))))))) (t (j (t (j (s (l 2) (s (l 2) (s (l 2) (j (l 2) (s (l 2) (l 14)))))) (s (t (l 2) (l 3)) (s (t (l 2) (s (l 3) (l 14))) (l 14)))) (s (s (l 3) (s (l 3) (j (j (t (l 2) (l 13)) (l 3)) (l 3)))) (j (s (j (s (t (l 2) (l 13)) (l 13)) (s (t (l 3) (l 13)) (s (j (l 13) (s (l 3) (l 13))) (l 13)))) (l 13)) (s (s (l 3) (s (l 3) (t (l 3) (s (l 3) (l 13))))) (t (j (t (l 14) (l 13)) (l 14)) (l 13)))))) (s (l 3) (s (l 3) (l 14)))) (j (s (t (s (l 3) (j (l 13) (s (l 3) (t (l 3) (l 13))))) (s (j (s (l 23) (t (l 13) (l 23))) (t (s (l 3) (t (l 3) (l 17))) (l 17))) (t (l 13) (t (l 13) (l 17))))) (t (l 13) (t (l 13) (l 17)))) (t (s (t (l 3) (j (s (l 3) (s (l 3) (l 17))) (s (t (l 3) (l 17)) (l 17)))) (t (j (s (s (l 3) (t (l 3) (l 13))) (l 13)) (l 14)) (s (l 17) (l 13)))) (s (l 17) (s (l 17) (l 13))))))) (t (s (s (s (s (l 23) (s (l 23) (s (l 23) (t (l 23) (j (l 23) (t (l 23) (l 17))))))) (j (s (l 23) (s (l 23) (s (l 23) (t (l 23) (j (l 23) (l 17)))))) (t (j (l 23) (l 17)) (l 17)))) (j (t (s (l 23) (j (l 23) (s (s (l 23) (l 17)) (l 17)))) (s (j (s (s (l 23) (s (l 23) (j (l 23) (l 17)))) (t (l 23) (l 17))) (l 17)) (l 17))) (l 17))) (j (s (s (s (t (t (j (l 23) (l 17)) (l 17)) (l 17)) (l 17)) (l 17)) (t (l 17) (q 17))) (t (s (l 17) (t (l 13) (s (j (l 17) (l 13)) (q 13)))) (s (t (s (l 17) (j (l 17) (s (l 17) (l 18)))) (s (j (l 17) (s (l 17) (l 18))) (q 17))) (q 17))))) (s (t (t (t (t (t (t (t (t (t (t (s (s (s (l 23) (l 16)) (l 16)) (s (l 16) (l 17))) (s (s (s (l 23) (l 16)) (l 16)) (s (l 16) (l 17)))) (s (s (s (l 23) (l 16)) (l 16)) (s (l 16) (l 17)))) (s (s (s (l 23) (l 16)) (l 16)) (s (l 16) (l 17)))) (s (l 16) (s (l 16) (l 17)))) (l 16)) (l 16)) (l 16)) (l 16)) (l 16)) (s (l 16) (q 16))) (q 17)))) (t (s (t (t (j (t (s (l 14) (j (t (l 14) (l 13)) (l 14))) (s (j (l 13) (l 14)) (s (j (l 13) (l 14)) (l 13)))) (l 14)) (j (s (s (s (s (s (s (t (t (j (l 13) (l 14)) (l 13)) (l 13)) (l 13)) (l 13)) (l 13)) (l 13)) (l 13)) (l 13)) (s (t (l 14) (j (s (s (l 14) (l 13)) (l 13)) (l 14))) (t (s (j (l 13) (l 14)) (s (j (l 13) (l 14)) (l 8))) (l 13))))) (j (s (t (l 13) (s (l 17) (t (j (l 17) (l 13)) (q 17)))) (t (j (t (s (l 13) (s (l 13) (l 12))) (s (s (l 13) (l 12)) (q 12))) (s (l 13) (t (l 13) (q 13)))) (q 13))) (s (l 13) (t (l 13) (q 13))))) (t (t (s (s (s (s (s (s (s (s (s (s (t (t (l 14) (l 8)) (l 8)) (l 8)) (l 8)) (l 8)) (l 8)) (l 8)) (l 8)) (l 8)) (l 8)) (l 8)) (l 8)) (s (s (s (s (t (l 8) (l 13)) (l 8)) (l 8)) (l 8)) (q 8))) (q 13))) (s (s (s (s (s (s (s (s (s (s (s (t (t (t (t (t (t (t (t (t (t (t (j (q 17) (q 13)) (k)) (k)) (k)) (k)) (k)) (k)) (k)) (k)) (k)) (k)) (k)) (k)) (k)) (k)) (k)) (k)) (k)) (k)) (k)) (k)) (k)) (k)))

open Tr in
def trmp0 : Tr := s (t (s (t (s (t (l 0) (t (t (l 0) (t (s (l 0) (s (l 0) (j (l 2) (s (l 0) (l 3))))) (s (l 0) (s (l 0) (j (l 2) (j (l 2) (l 3))))))) (s (l 2) (s (l 2) (s (l 2) (s (l 2) (j (l 2) (t (l 3) (l 2))))))))) (t (s (s (l 0) (s (t (l 0) (t (l 0) (j (l 2) (l 3)))) (s (t (l 0) (t (l 0) (j (l 2) (l 3)))) (l 3)))) (l 3)) (j (l 2) (l 3)))) (s (s (l 2) (s (l 2) (t (l 2) (t (l 2) (t (s (l 2) (t (l 2) (s (t (l 2) (l 21)) (l 21)))) (s (t (s (l 2) (s (l 2) (l 21))) (l 21)) (l 21))))))) (t (j (l 2) (j (s (l 2) (t (l 2) (s (l 2) (l 21)))) (s (s (l 2) (l 3)) (l 3)))) (j (l 21) (j (l 21) (t (j (s (s (l 2) (l 21)) (l 21)) (s (t (l 3) (j (t (l 3) (l 21)) (l 3))) (t (l 3) (l 21)))) (s (s (s (s (s (j (l 21) (j (l 21) (l 22))) (l 21)) (l 21)) (l 21)) (l 21)) (l 21)))))))) (t (t (s (l 3) (s (l 3) (s (l 3) (t (l 3) (t (l 3) (l 15)))))) (s (j (j (l 2) (j (t (l 3) (s (l 2) (s (l 2) (l 15)))) (l 3))) (l 3)) (s (t (t (s (l 3) (t (l 3) (l 15))) (s (s (t (t (l 3) (s (t (l 3) (l 15)) (l 15))) (l 15)) (l 15)) (l 15))) (l 15)) (l 15)))) (j (s (s (t (s (l 2) (t (l 2) (l 15))) (s (l 21) (s (l 21) (j (t (l 15) (l 21)) (l 21))))) (t (l 15) (j (l 15) (s (l 21) (s (l 21) (s (l 21) (t (l 15) (t (l 21) (l 20))))))))) (t (l 15) (t (l 15) (s (t (t (l 15) (l 20)) (l 20)) (l 20))))) (t (j (s (t (t (s (l 3) (l 15)) (s (t (l 3) (l 21)) (l 15))) (l 21)) (s (l 15) (s (l 15) (s (l 15) (t (l 15) (t (l 15) (l 9))))))) (s (t (l 3) (s (t (l 3) (l 21)) (l 21))) (t (t (l 15) (j (l 15) (s (l 21) (l 9)))) (s (l 21) (l 9))))) (s (l 21) (s (s (l 21) (s (l 21) (t (l 21) (l 9)))) (s (t (s (t (j (j (l 15) (l 21)) (l 9)) (l 9)) (s (s (t (t (t (j (j (l 15) (l 9)) (l 9)) (l 9)) (l 9)) (l 9)) (l 9)) (l 9))) (l 9)) (l 9)))))))) (s (t (s (j (l 21) (s (j (s (j (l 21) (l 22)) (l 21)) (s (l 22) (t (l 22) (l 21)))) (s (t (j (l 21) (l 22)) (l 21)) (l 21)))) (t (l 21) (t (s (l 21) (j (j (l 20) (l 21)) (l 21))) (j (s (t (l 21) (s (l 16) (s (l 16) (l 20)))) (l 20)) (s (l 21) (s (l 21) (j (s (l 21) (l 20)) (l 21)))))))) (t (t (t (t (t (t (t (t (t (t (s (s (s (s (j (l 21) (l 22)) (l 16)) (l 16)) (l 21)) (s (l 16) (s (l 16) (s (l 16) (l 20))))) (s (s (s (s (j (l 21) (l 22)) (l 16)) (l 16)) (l 21)) (s (l 16) (s (l 16) (s (l 16) (l 20)))))) (s (s (s (s (j (l 21) (l 22)) (l 16)) (l 16)) (l 21)) (s (l 16) (s (l 16) (s (l 16) (l 20)))))) (s (s (s (s (j (l 21) (l 22)) (l 16)) (l 16)) (l 16)) (s (l 16) (s (l 16) (s (l 16) (l 20)))))) (s (l 16) (s (l 16) (s (l 16) (s (l 16) (l 20)))))) (l 16)) (l 16)) (l 16)) (l 16)) (l 16)) (s (l 16) (q 16)))) (t (j (s (s (t (j (l 20) (t (l 21) (s (l 21) (l 20)))) (l 20)) (l 20)) (l 20)) (s (t (s (l 21) (s (l 21) (s (l 21) (t (l 21) (j (l 20) (l 21)))))) (j (s (t (s (l 21) (l 20)) (l 20)) (l 20)) (t (s (l 21) (s (l 21) (l 20))) (s (s (l 21) (l 20)) (q 21))))) (t (s (s (t (s (l 21) (s (l 21) (l 9))) (j (l 20) (l 21))) (l 9)) (l 9)) (q 20)))) (q 20)))) (t (t (s (s (t (t (j (s (l 3) (t (l 14) (l 15))) (l 15)) (l 15)) (s (l 15) (s (l 15) (s (l 15) (t (l 15) (t (l 15) (j (l 15) (t (l 15) (l 9))))))))) (t (t (t (j (t (l 14) (l 15)) (l 15)) (l 15)) (l 15)) (s (t (l 15) (j (l 15) (j (l 15) (l 9)))) (j (s (l 15) (s (l 15) (s (l 15) (t (l 15) (t (l 15) (t (l 15) (l 9))))))) (t (j (l 15) (s (t (l 15) (l 9)) (l 8))) (l 9)))))) (t (s (s (s (s (s (s (s (s (s (s (t (t (t (t (t (t (t (t (t (j (l 14) (l 15)) (l 8)) (l 8)) (l 8)) (l 8)) (l 8)) (l 8)) (l 8)) (l 8)) (l 8)) (l 8)) (l 8)) (l 8)) (l 8)) (l 8)) (l 8)) (l 8)) (l 8)) (l 8)) (l 8)) (s (s (s (s (s (t (l 8) (t (l 8) (t (l 8) (l 9)))) (l 8)) (l 8)) (l 8)) (l 8)) (q 8)))) (s (j (t (s (s (l 15) (s (l 15) (s (l 15) (s (l 15) (t (l 15) (t (l 15) (l 9))))))) (t (s (l 15) (j (s (l 15) (l 9)) (l 9))) (s (j (s (l 15) (l 9)) (l 9)) (q 9)))) (s (t (t (s (l 15) (j (l 15) (l 9))) (l 20)) (l 20)) (q 9))) (s (t (j (t (s (l 15) (s (l 15) (l 9))) (s (t (l 15) (l 9)) (l 9))) (l 9)) (l 9)) (t (l 9) (q 9)))) (q 9))) (s (s (s (s (s (s (s (s (s (s (s (t (t (t (t (t (t (t (t (t (t (t (j (q 20) (q 9)) (k)) (k)) (k)) (k)) (k)) (k)) (k)) (k)) (k)) (k)) (k)) (k)) (k)) (k)) (k)) (k)) (k)) (k)) (k)) (k)) (k)) (k)))

open Tr in
def trmp1 : Tr := t (s (t (j (t (s (s (l 0) (t (s (l 0) (s (s (l 0) (s (l 0) (t (l 0) (j (l 3) (l 4))))) (j (t (l 4) (l 3)) (l 4)))) (t (s (l 0) (j (l 3) (l 4))) (l 3)))) (j (s (l 3) (l 15)) (s (l 4) (s (l 4) (j (s (j (l 15) (l 4)) (l 15)) (l 4)))))) (s (s (s (t (l 0) (t (s (l 0) (l 3)) (s (j (l 2) (l 3)) (l 3)))) (l 3)) (l 3)) (s (s (l 3) (s (l 3) (s (l 3) (j (l 3) (j (l 3) (t (l 4) (l 9))))))) (j (s (l 3) (t (l 15) (j (t (l 15) (l 9)) (l 9)))) (t (s (j (s (l 3) (j (l 3) (s (l 3) (l 9)))) (s (l 4) (l 9))) (s (s (s (s (s (t (t (t (t (l 4) (l 9)) (l 9)) (l 9)) (l 9)) (l 9)) (l 9)) (l 9)) (l 9)) (l 9))) (s (s (j (l 3) (l 9)) (l 9)) (l 9))))))) (s (s (t (l 0) (t (s (l 0) (j (s (l 0) (l 3)) (s (l 0) (l 4)))) (s (l 3) (j (l 3) (l 4))))) (s (t (t (l 0) (s (l 0) (l 4))) (j (j (l 3) (l 4)) (l 4))) (l 4))) (t (l 4) (s (s (l 4) (s (l 4) (s (l 4) (l 9)))) (l 9))))) (s (s (t (l 3) (j (j (s (l 22) (t (l 3) (l 22))) (l 3)) (s (l 3) (j (l 3) (j (l 3) (t (j (l 3) (l 4)) (l 23))))))) (t (j (l 3) (j (s (l 3) (t (l 3) (l 22))) (t (l 4) (t (l 4) (t (l 4) (j (s (l 3) (l 22)) (l 4))))))) (t (j (l 3) (j (l 22) (j (s (s (l 3) (l 22)) (l 22)) (t (l 4) (s (t (l 4) (j (j (l 22) (l 4)) (l 4))) (l 22)))))) (s (s (t (j (l 22) (j (l 22) (j (l 22) (j (l 22) (l 23))))) (l 22)) (l 22)) (j (j (j (l 21) (s (l 22) (s (l 22) (l 21)))) (l 22)) (l 22)))))) (j (s (t (s (l 3) (j (s (l 3) (s (l 3) (t (l 3) (l 9)))) (s (t (l 3) (l 9)) (l 9)))) (j (s (t (t (l 3) (s (t (l 3) (l 21)) (l 21))) (l 21)) (l 21)) (s (s (l 22) (j (t (l 9) (l 21)) (l 22))) (t (l 9) (t (l 9) (l 21)))))) (s (s (t (t (j (l 3) (l 9)) (l 9)) (t (l 9) (l 21))) (t (s (s (s (s (s (s (s (t (j (l 3) (l 9)) (l 9)) (l 9)) (l 9)) (l 9)) (l 9)) (l 9)) (l 9)) (l 9)) (t (l 9) (l 21)))) (t (l 9) (l 21)))) (s (t (j (t (s (j (s (l 3) (l 9)) (s (l 4) (l 9))) (l 9)) (s (l 22) (s (l 22) (l 9)))) (t (l 4) (t (s (l 4) (l 22)) (l 22)))) (l 22)) (j (t (l 9) (s (j (t (l 9) (s (j (l 21) (l 22)) (l 21))) (l 22)) (j (t (s (l 9) (t (l 9) (l 21))) (l 21)) (s (s (t (l 22) (l 10)) (l 10)) (l 10))))) (t (t (j (l 9) (t (s (l 4) (l 9)) (s (s (l 4) (l 22)) (l 10)))) (s (l 22) (s (l 22) (l 10)))) (s (l 22) (l 10)))))))) (t (s (s (j (t (t (l 15) (j (l 15) (j (l 15) (l 9)))) (t (j (j (l 15) (l 9)) (l 9)) (l 9))) (s (l 9) (s (l 9) (t (l 9) (t (l 9) (j (l 9) (t (l 9) (l 10)))))))) (s (t (j (j (l 15) (t (l 15) (l 9))) (l 9)) (t (l 9) (j (l 9) (j (l 9) (l 10))))) (s (t (j (j (s (l 15) (s (l 15) (t (l 15) (t (l 15) (l 9))))) (t (l 15) (l 9))) (l 9)) (j (l 9) (j (s (l 9) (t (l 9) (t (l 9) (l 10)))) (t (t (l 9) (l 10)) (l 10))))) (s (t (j (t (s (l 15) (t (l 15) (j (l 15) (l 9)))) (s (t (j (l 15) (l 9)) (l 9)) (l 8))) (l 9)) (t (l 8) (j (l 9) (t (j (l 9) (l 10)) (l 10))))) (s (t (t (j (t (l 15) (t (l 15) (l 8))) (l 9)) (l 8)) (t (l 8) (j (l 9) (t (l 8) (l 10))))) (s (s (t (t (t (j (l 15) (l 9)) (l 8)) (l 8)) (t (l 8) (j (l 9) (l 10)))) (s (t (t (t (j (l 15) (l 9)) (l 8)) (l 8)) (t (l 8) (j (l 9) (l 10)))) (s (t (t (t (j (l 15) (l 9)) (l 8)) (l 8)) (t (l 8) (j (l 9) (l 10)))) (s (t (t (t (j (l 15) (l 9)) (l 8)) (l 8)) (t (l 8) (j (l 9) (l 10)))) (t (t (t (j (l 15) (l 9)) (l 8)) (l 8)) (t (l 8) (j (l 9) (l 10)))))))) (s (s (s (s (t (t (t (j (l 15) (l 9)) (l 8)) (l 8)) (t (l 8) (j (l 9) (l 10)))) (t (t (t (j (l 15) (l 9)) (l 8)) (l 8)) (t (l 8) (j (l 9) (l 10))))) (t (t (t (j (l 15) (l 9)) (l 8)) (l 8)) (t (l 8) (j (l 9) (l 10))))) (t (t (t (j (l 15) (l 9)) (l 8)) (l 8)) (t (l 8) (j (l 9) (l 10))))) (t (t (t (j (l 15) (l 9)) (l 8)) (l 8)) (t (l 8) (j (l 9) (l 10))))))))))) (t (s (s (s (s (s (s (s (s (s (s (t (t (t (t (t (t (t (t (t (j (l 15) (l 9)) (l 8)) (l 8)) (l 8)) (l 8)) (l 8)) (l 8)) (l 8)) (l 8)) (l 8)) (l 8)) (l 8)) (l 8)) (l 8)) (l 8)) (l 8)) (l 8)) (l 8)) (l 8)) (l 8)) (s (s (s (s (s (t (l 8) (j (l 9) (l 10))) (l 8)) (l 8)) (l 8)) (l 8)) (q 8)))) (s (j (j (s (l 9) (t (l 9) (q 9))) (t (s (l 9) (t (s (l 9) (j (l 9) (l 10))) (s (s (l 9) (l 10)) (q 9)))) (s (l 21) (q 9)))) (s (t (j (t (l 9) (j (s (l 9) (l 10)) (s (t (l 9) (l 10)) (l 10)))) (s (s (s (t (j (l 9) (l 10)) (l 10)) (l 10)) (l 10)) (l 10))) (l 10)) (t (s (s (s (s (s (s (s (t (j (l 9) (l 10)) (l 10)) (l 10)) (l 10)) (l 10)) (l 10)) (l 10)) (l 10)) (l 10)) (q 10)))) (s (s (s (s (s (s (s (s (s (s (t (t (t (t (t (t (t (t (t (t (j (q 9) (q 10)) (k)) (k)) (k)) (k)) (k)) (k)) (k)) (k)) (k)) (k)) (k)) (k)) (k)) (k)) (k)) (k)) (k)) (k)) (k)) (k))))) (s (t (s (t (s (j (l 22) (j (l 22) (s (l 23) (j (l 22) (l 23))))) (j (j (s (j (l 21) (l 22)) (l 21)) (s (l 22) (s (l 22) (t (l 22) (l 21))))) (l 22))) (s (s (j (l 22) (j (l 22) (j (l 22) (l 23)))) (s (l 22) (t (l 22) (t (l 22) (s (t (l 22) (l 16)) (l 16)))))) (j (s (j (l 21) (j (t (l 22) (l 21)) (s (l 22) (t (l 22) (l 21))))) (l 21)) (s (l 22) (t (l 22) (t (s (l 22) (j (l 21) (l 22))) (j (j (l 21) (s (l 22) (l 21))) (l 22)))))))) (j (s (s (s (s (t (t (j (l 21) (l 22)) (l 21)) (l 21)) (l 21)) (l 21)) (l 21)) (t (l 21) (q 21))) (j (t (s (s (l 22) (j (s (t (l 22) (l 21)) (l 21)) (t (l 22) (l 21)))) (s (s (s (s (t (j (l 21) (l 22)) (l 21)) (l 21)) (l 21)) (l 21)) (l 21))) (s (s (s (s (t (l 22) (l 21)) (l 21)) (l 21)) (l 21)) (q 21))) (t (s (l 22) (l 10)) (s (t (s (l 22) (j (l 21) (l 22))) (s (j (l 21) (l 22)) (q 22))) (q 22)))))) (s (t (t (t (t (t (t (t (t (t (t (s (s (s (s (s (j (l 22) (j (l 22) (l 23))) (l 16)) (l 16)) (l 16)) (l 16)) (s (l 16) (s (l 16) (s (l 16) (s (l 16) (l 21)))))) (s (s (s (s (s (s (j (l 22) (j (l 22) (l 23))) (l 16)) (l 16)) (l 16)) (l 16)) (l 16)) (s (l 16) (s (l 16) (s (l 16) (s (l 16) (l 21))))))) (s (s (s (s (s (s (j (l 22) (j (l 22) (l 23))) (l 16)) (l 16)) (l 16)) (l 16)) (l 16)) (s (l 16) (s (l 16) (s (l 16) (s (l 16) (l 21))))))) (s (s (s (s (s (s (s (j (l 22) (j (l 22) (l 23))) (l 16)) (l 16)) (l 16)) (l 16)) (l 16)) (l 16)) (s (l 16) (s (l 16) (s (l 16) (s (l 16) (l 21))))))) (s (l 16) (s (l 16) (s (l 16) (s (l 16) (s (l 16) (l 21))))))) (l 16)) (l 16)) (l 16)) (l 16)) (l 16)) (s (l 16) (q 16))) (q 21))) (s (s (s (s (s (s (s (s (s (s (s (t (t (t (t (t (t (t (t (t (t (t (j (q 21) (q 10)) (k)) (k)) (k)) (k)) (k)) (k)) (k)) (k)) (k)) (k)) (k)) (k)) (k)) (k)) (k)) (k)) (k)) (k)) (k)) (k)) (k)) (k)))

open Tr in
def trmp2 : Tr := t (s (t (j (j (t (s (s (l 0) (t (s (l 0) (t (s (l 0) (l 5)) (j (l 4) (l 5)))) (s (s (l 0) (l 4)) (l 4)))) (s (t (l 5) (l 4)) (s (t (s (l 5) (l 9)) (s (l 4) (t (l 9) (s (l 4) (l 9))))) (l 9)))) (s (s (s (t (l 0) (t (s (l 0) (l 4)) (j (l 3) (l 4)))) (l 4)) (l 4)) (s (l 4) (s (s (l 4) (s (l 4) (t (l 4) (j (l 4) (l 10))))) (t (j (l 9) (j (t (l 9) (l 10)) (l 10))) (s (j (t (l 4) (l 10)) (l 10)) (l 10))))))) (s (t (s (l 0) (s (s (l 0) (s (s (s (l 0) (s (l 0) (t (l 0) (t (l 0) (l 4))))) (s (t (l 0) (t (l 0) (l 4))) (l 5))) (l 5))) (l 5))) (s (t (s (l 0) (l 4)) (l 4)) (l 4))) (t (s (l 5) (s (l 5) (s (l 5) (s (l 5) (t (l 5) (t (l 5) (l 10))))))) (s (j (l 4) (t (l 5) (s (l 4) (l 10)))) (s (t (t (s (l 5) (s (l 5) (l 10))) (s (s (t (l 5) (l 10)) (l 10)) (l 10))) (l 10)) (l 10)))))) (s (s (t (l 0) (t (s (l 0) (s (l 0) (t (l 0) (j (l 4) (l 5))))) (s (l 4) (j (l 4) (l 5))))) (s (t (t (l 0) (l 5)) (s (s (s (t (l 5) (j (l 4) (l 5))) (l 5)) (l 5)) (l 5))) (l 5))) (s (l 5) (t (l 5) (l 10))))) (s (j (t (l 4) (t (s (j (l 23) (l 4)) (l 4)) (s (l 23) (s (l 23) (j (j (j (l 22) (s (l 23) (l 22))) (l 23)) (l 23)))))) (j (s (l 4) (t (j (l 4) (j (s (l 4) (t (l 5) (s (l 4) (l 23)))) (s (l 4) (l 5)))) (s (t (s (l 4) (l 23)) (l 23)) (l 23)))) (s (s (l 4) (t (l 4) (j (s (l 4) (s (l 4) (t (l 4) (t (l 4) (l 23))))) (t (s (l 4) (l 5)) (l 17))))) (t (l 5) (t (j (t (s (s (l 4) (j (l 23) (l 5))) (l 23)) (s (s (s (l 4) (l 23)) (l 23)) (l 23))) (s (l 5) (t (l 5) (l 23)))) (s (j (l 23) (s (l 17) (l 23))) (l 23))))))) (j (s (t (j (s (l 4) (s (l 4) (t (l 4) (t (l 4) (l 10))))) (s (s (l 4) (t (l 4) (l 10))) (l 10))) (s (j (t (t (l 4) (j (l 22) (s (l 4) (l 10)))) (s (s (j (l 22) (l 23)) (l 22)) (l 22))) (l 23)) (t (s (s (s (s (s (s (s (t (j (l 4) (l 10)) (l 10)) (l 10)) (l 10)) (l 10)) (l 10)) (l 10)) (l 10)) (l 10)) (t (j (l 22) (j (l 10) (l 23))) (s (j (l 22) (j (l 22) (l 23))) (l 22)))))) (t (s (s (t (j (t (l 4) (l 10)) (l 10)) (l 10)) (l 10)) (l 10)) (t (l 10) (s (t (t (l 10) (l 22)) (l 22)) (l 22))))) (t (t (s (j (j (t (s (l 5) (l 10)) (l 23)) (s (l 5) (l 10))) (l 5)) (j (l 10) (t (s (l 5) (j (l 10) (l 11))) (j (s (l 23) (l 10)) (j (l 23) (j (l 23) (l 11))))))) (j (s (l 23) (t (l 10) (j (l 10) (j (l 10) (l 23))))) (s (s (s (l 5) (t (l 5) (l 23))) (s (t (l 5) (l 23)) (l 23))) (l 23)))) (s (l 23) (s (s (l 23) (s (l 23) (t (l 23) (t (s (l 23) (l 11)) (l 11))))) (s (t (s (j (j (j (l 10) (l 23)) (l 23)) (l 11)) (t (j (j (l 10) (l 11)) (l 11)) (l 11))) (l 11)) (l 11)))))))) (t (s (s (j (t (j (l 9) (j (t (l 9) (l 10)) (s (s (l 5) (l 10)) (l 10)))) (s (t (j (t (l 9) (l 10)) (l 10)) (l 10)) (l 10))) (s (l 10) (t (l 10) (t (l 10) (j (l 10) (l 11)))))) (s (t (j (j (l 9) (l 10)) (l 10)) (j (l 10) (j (s (l 10) (s (l 10) (s (l 10) (t (l 10) (t (l 10) (l 11)))))) (t (t (l 10) (l 11)) (l 11))))) (s (t (j (j (t (l 9) (t (l 9) (l 10))) (l 10)) (l 10)) (j (l 10) (t (j (l 10) (t (l 10) (l 11))) (s (s (s (s (s (s (t (j (l 10) (l 11)) (l 11)) (l 11)) (l 11)) (l 11)) (l 11)) (l 11)) (l 11))))) (s (t (j (t (j (l 9) (l 10)) (s (t (j (l 9) (l 10)) (l 10)) (l 8))) (l 10)) (t (l 8) (j (l 10) (l 11)))) (s (t (t (j (t (l 9) (j (l 9) (l 10))) (l 10)) (l 8)) (t (l 8) (j (l 10) (l 11)))) (s (s (t (t (t (j (l 9) (l 10)) (l 8)) (l 8)) (t (l 8) (j (l 10) (l 11)))) (s (t (t (t (j (l 9) (l 10)) (l 8)) (l 8)) (t (l 8) (j (l 10) (l 11)))) (s (t (t (t (j (l 9) (l 10)) (l 8)) (l 8)) (t (l 8) (j (l 10) (l 11)))) (s (t (t (t (j (l 9) (l 10)) (l 8)) (l 8)) (t (l 8) (j (l 10) (l 11)))) (t (t (t (j (l 9) (l 10)) (l 8)) (l 8)) (t (l 8) (j (l 10) (l 11)))))))) (s (s (s (s (t (t (t (j (l 9) (l 10)) (l 8)) (l 8)) (t (l 8) (j (l 10) (l 11)))) (t (t (t (j (l 9) (l 10)) (l 8)) (l 8)) (t (l 8) (j (l 10) (l 11))))) (t (t (t (j (l 9) (l 10)) (l 8)) (l 8)) (t (l 8) (j (l 10) (l 11))))) (t (t (t (j (l 9) (l 10)) (l 8)) (l 8)) (t (l 8) (j (l 10) (l 11))))) (t (t (t (j (l 9) (l 10)) (l 8)) (l 8)) (t (l 8) (j (s (l 10) (t (l 10) (j (l 10) (l 11)))) (l 11))))))))))) (t (s (s (s (s (s (s (s (s (s (s (t (t (t (t (t (t (t (t (t (j (l 9) (l 10)) (l 8)) (l 8)) (l 8)) (l 8)) (l 8)) (l 8)) (l 8)) (l 8)) (l 8)) (l 8)) (l 8)) (l 8)) (l 8)) (l 8)) (l 8)) (l 8)) (l 8)) (l 8)) (l 8)) (s (s (s (s (s (t (l 8) (t (l 8) (t (l 8) (t (l 8) (t (l 8) (s (j (j (l 10) (l 11)) (l 11)) (q 8))))))) (l 8)) (l 8)) (l 8)) (l 8)) (q 8)))) (s (j (s (t (l 10) (j (j (l 10) (l 22)) (t (t (s (l 10) (s (l 22) (l 11))) (l 22)) (l 22)))) (t (j (s (l 10) (t (l 10) (q 10))) (t (s (l 10) (s (t (l 10) (l 11)) (l 11))) (l 11))) (q 10))) (s (t (j (t (s (l 10) (s (l 10) (l 11))) (s (j (s (l 10) (l 11)) (l 11)) (l 11))) (l 11)) (l 11)) (t (l 11) (q 11)))) (s (s (s (s (s (s (s (s (s (s (t (t (t (t (t (t (t (t (t (t (j (j (q 10) (q 11)) (q 11)) (k)) (k)) (k)) (k)) (k)) (k)) (k)) (k)) (k)) (k)) (k)) (k)) (k)) (k)) (k)) (k)) (k)) (k)) (k)) (k))))) (s (t (s (t (s (j (l 23) (j (s (t (l 4) (l 23)) (l 23)) (l 17))) (j (j (s (s (l 23) (t (l 23) (l 22))) (s (j (l 22) (l 23)) (l 22))) (l 23)) (l 23))) (s (s (j (l 23) (j (l 23) (l 17))) (s (l 23) (t (l 23) (t (l 23) (s (s (l 23) (l 16)) (l 16)))))) (j (j (l 22) (s (s (l 23) (j (t (l 23) (l 22)) (l 23))) (s (t (l 23) (l 22)) (l 22)))) (s (l 23) (s (l 23) (t (l 23) (j (t (l 23) (l 22)) (l 23)))))))) (j (s (s (t (j (l 22) (j (l 22) (t (l 23) (l 22)))) (l 22)) (l 22)) (t (l 22) (q 22))) (s (t (s (l 23) (s (l 23) (t (l 23) (j (l 22) (l 23))))) (j (s (t (s (l 23) (l 22)) (l 22)) (l 22)) (s (l 23) (t (l 23) (q 23))))) (t (s (s (t (s (l 23) (t (l 23) (j (l 22) (l 23)))) (j (l 22) (l 23))) (l 11)) (t (l 11) (q 11))) (q 22))))) (s (t (t (t (t (t (t (t (t (t (t (s (s (s (s (j (l 23) (l 17)) (l 16)) (l 16)) (l 16)) (s (l 16) (s (l 16) (s (l 16) (s (l 16) (s (s (l 16) (s (l 16) (s (l 16) (s (l 16) (j (l 22) (j (l 22) (l 23))))))) (s (s (j (l 22) (j (l 22) (l 23))) (s (j (l 22) (j (l 22) (l 23))) (l 22))) (l 22)))))))) (s (s (s (s (j (l 23) (l 17)) (l 16)) (l 16)) (l 16)) (s (l 16) (s (l 16) (s (l 16) (s (l 16) (s (l 16) (s (s (j (l 22) (j (l 22) (l 23))) (s (j (l 22) (j (l 22) (l 23))) (l 22))) (l 22))))))))) (s (s (s (s (j (l 23) (l 17)) (l 16)) (l 16)) (l 16)) (s (l 16) (s (l 16) (s (l 16) (s (l 16) (s (l 16) (s (s (j (l 22) (j (l 22) (l 23))) (s (s (t (j (l 22) (j (l 22) (l 23))) (l 22)) (l 22)) (l 22))) (l 22))))))))) (s (s (s (s (j (l 23) (l 17)) (l 16)) (l 16)) (l 16)) (s (l 16) (s (l 16) (s (l 16) (s (l 16) (s (l 16) (s (s (l 16) (l 22)) (l 22))))))))) (s (l 16) (s (l 16) (s (l 16) (s (l 16) (s (l 16) (s (l 16) (s (l 16) (q 22))))))))) (l 16)) (l 16)) (l 16)) (l 16)) (l 16)) (s (l 16) (q 16))) (q 22))) (s (s (s (s (s (s (s (s (s (s (s (t (t (t (t (t (t (t (t (t (t (t (j (q 22) (q 11)) (k)) (k)) (k)) (k)) (k)) (k)) (k)) (k)) (k)) (k)) (k)) (k)) (k)) (k)) (k)) (k)) (k)) (k)) (k)) (k)) (k)) (k)))

open Tr in
def trmp3 : Tr := t (s (t (j (t (s (s (l 0) (t (s (l 0) (s (s (l 0) (s (l 0) (l 6))) (l 6))) (s (t (l 0) (l 5)) (l 5)))) (j (s (t (l 6) (l 5)) (s (t (l 6) (l 5)) (l 10))) (s (l 6) (s (l 6) (j (s (l 6) (l 10)) (l 6)))))) (s (s (t (s (l 0) (l 5)) (s (t (s (l 0) (l 5)) (l 5)) (l 5))) (l 5)) (s (s (l 5) (s (l 5) (s (l 5) (s (l 5) (s (l 5) (t (t (j (l 5) (l 6)) (l 5)) (l 5))))))) (j (s (l 5) (t (t (l 10) (j (l 10) (l 11))) (s (s (j (l 5) (l 11)) (l 11)) (l 11)))) (s (j (s (l 5) (s (j (l 5) (l 11)) (l 11))) (s (t (l 6) (l 11)) (l 11))) (l 11)))))) (s (s (t (l 0) (t (t (l 0) (l 5)) (l 5))) (s (t (s (l 0) (t (l 0) (l 6))) (j (l 5) (l 6))) (s (t (l 6) (t (l 6) (l 5))) (l 6)))) (t (l 6) (s (s (l 6) (t (l 6) (l 11))) (l 11))))) (s (t (s (l 5) (s (l 5) (s (l 5) (s (l 5) (t (l 5) (j (l 5) (l 17))))))) (s (j (t (l 5) (l 17)) (l 5)) (j (t (l 5) (s (l 17) (s (l 17) (j (j (l 23) (l 17)) (l 17))))) (l 17)))) (j (s (t (s (l 5) (j (s (l 5) (t (l 5) (l 11))) (s (s (l 5) (l 11)) (l 11)))) (s (j (t (s (l 5) (t (l 5) (l 23))) (l 23)) (s (l 17) (t (l 11) (s (l 17) (t (l 11) (l 23)))))) (s (t (l 11) (t (l 11) (l 23))) (l 11)))) (s (s (s (s (t (t (j (l 5) (l 11)) (l 11)) (l 11)) (l 11)) (l 11)) (l 11)) (t (l 11) (l 23)))) (j (t (s (s (s (l 5) (l 11)) (l 11)) (l 11)) (s (l 17) (t (s (l 11) (s (l 11) (j (l 11) (t (l 11) (l 12))))) (s (t (j (l 11) (s (l 17) (s (l 17) (l 23)))) (l 23)) (l 23))))) (t (s (t (s (l 6) (l 11)) (l 17)) (s (l 11) (s (l 11) (s (l 11) (s (l 11) (t (l 11) (l 12))))))) (s (l 17) (s (l 17) (s (s (t (l 17) (l 12)) (l 12)) (l 12))))))))) (t (s (t (j (t (s (l 10) (s (l 10) (s (l 10) (s (l 10) (t (l 10) (t (l 10) (l 8))))))) (s (j (l 10) (t (l 10) (l 11))) (t (j (j (l 10) (l 11)) (l 11)) (l 11)))) (l 11)) (s (s (s (t (t (j (j (l 10) (l 11)) (l 11)) (l 11)) (l 11)) (l 11)) (l 11)) (s (l 11) (s (t (l 11) (t (l 11) (j (l 11) (l 12)))) (t (l 11) (j (l 11) (t (j (l 11) (l 12)) (l 12)))))))) (t (s (s (s (s (s (s (s (s (s (s (t (t (t (t (t (t (t (t (t (j (l 10) (l 11)) (l 8)) (l 8)) (l 8)) (l 8)) (l 8)) (l 8)) (l 8)) (l 8)) (l 8)) (l 8)) (l 8)) (l 8)) (l 8)) (l 8)) (l 8)) (l 8)) (l 8)) (l 8)) (l 8)) (s (s (s (s (s (t (l 8) (j (l 11) (l 12))) (l 8)) (l 8)) (l 8)) (l 8)) (q 8)))) (s (j (s (t (l 11) (j (j (l 11) (l 23)) (l 23))) (t (j (s (l 11) (t (l 11) (q 11))) (t (s (l 11) (s (l 11) (l 12))) (s (s (l 11) (l 12)) (q 12)))) (q 11))) (s (t (t (s (l 11) (j (l 11) (l 12))) (j (s (l 11) (l 12)) (l 12))) (s (s (s (s (t (t (j (l 11) (l 12)) (l 12)) (l 12)) (l 12)) (l 12)) (l 12)) (l 12))) (s (s (s (s (t (t (t (l 11) (l 12)) (l 12)) (q 12)) (l 12)) (l 12)) (l 12)) (l 12)))) (s (s (s (s (s (s (s (s (s (s (t (t (t (t (t (t (t (t (t (t (j (q 11) (q 12)) (k)) (k)) (k)) (k)) (k)) (k)) (k)) (k)) (k)) (k)) (k)) (k)) (k)) (k)) (k)) (k)) (k)) (k)) (k)) (k))))) (s (t (s (s (s (s (s (s (s (t (t (j (l 17) (l 5)) (l 17)) (l 17)) (l 17)) (l 17)) (l 17)) (l 17)) (s (l 17) (s (l 17) (t (l 17) (t (l 17) (t (l 17) (l 16))))))) (t (s (l 17) (j (j (l 23) (l 17)) (l 17))) (j (s (j (l 23) (s (l 17) (t (l 17) (l 23)))) (l 23)) (s (l 17) (j (t (l 17) (l 23)) (s (l 17) (s (l 17) (t (l 17) (l 23))))))))) (s (j (s (s (s (s (t (j (l 23) (l 17)) (l 23)) (l 23)) (l 23)) (l 23)) (l 23)) (t (s (l 17) (j (s (t (l 17) (l 23)) (l 23)) (s (l 17) (t (l 17) (l 23))))) (s (s (t (s (l 17) (l 23)) (l 23)) (l 23)) (l 23)))) (t (s (s (t (t (j (l 23) (j (l 23) (l 17))) (l 23)) (l 23)) (l 23)) (l 23)) (q 23)))) (s (t (t (t (t (t (t (t (t (t (t (s (s (l 17) (l 16)) (s (l 16) (s (l 16) (l 23)))) (s (s (l 17) (l 16)) (s (l 16) (s (l 16) (l 23))))) (s (s (l 17) (l 16)) (s (l 16) (s (l 16) (l 23))))) (s (s (l 17) (l 16)) (s (l 16) (s (l 16) (l 23))))) (s (l 16) (s (l 16) (s (l 16) (l 23))))) (l 16)) (l 16)) (l 16)) (l 16)) (l 16)) (s (l 16) (q 16))) (q 23))) (q 23))

open Tr in
def trmm0 : Tr := s (t (s (s (t (t (l 0) (s (t (l 0) (j (l 5) (t (s (l 0) (l 6)) (l 6)))) (s (t (l 0) (l 6)) (l 6)))) (j (s (l 5) (j (s (l 5) (s (l 5) (s (l 5) (t (l 5) (t (l 5) (l 17)))))) (t (l 6) (t (s (l 5) (l 6)) (l 18))))) (s (t (l 6) (t (l 6) (l 18))) (l 6)))) (t (t (t (s (l 0) (j (s (s (l 0) (l 6)) (l 6)) (s (s (l 0) (l 7)) (l 7)))) (t (s (l 0) (t (t (j (l 6) (j (l 6) (l 7))) (l 6)) (l 6))) (l 6))) (l 6)) (t (s (s (s (s (s (s (t (l 6) (t (l 6) (t (l 6) (t (l 6) (t (l 6) (t (l 6) (t (l 6) (j (j (l 5) (l 6)) (l 6))))))))) (l 6)) (l 6)) (l 6)) (l 6)) (l 6)) (l 6)) (j (t (j (t (j (s (l 5) (l 17)) (s (l 6) (l 17))) (s (s (l 5) (l 17)) (l 17))) (s (l 6) (j (s (l 6) (l 17)) (l 6)))) (s (j (l 17) (j (s (s (l 18) (l 17)) (l 17)) (l 18))) (l 17))) (t (l 6) (s (l 18) (s (l 18) (s (l 18) (j (j (l 17) (l 18)) (l 18)))))))))) (t (j (s (l 6) (s (l 6) (l 11))) (t (j (s (t (l 7) (l 6)) (s (t (l 7) (s (l 6) (l 11))) (l 11))) (s (l 7) (s (l 7) (s (l 7) (j (s (l 7) (l 11)) (l 7)))))) (s (s (l 6) (s (l 6) (j (l 6) (j (l 6) (t (l 7) (l 12)))))) (j (s (s (l 6) (s (l 6) (t (l 6) (s (l 6) (l 12))))) (t (j (l 11) (t (l 11) (l 12))) (l 12))) (s (j (s (t (l 6) (l 12)) (s (j (s (l 6) (l 12)) (l 12)) (l 12))) (s (t (l 7) (l 12)) (l 12))) (l 12)))))) (j (t (s (t (l 6) (j (s (t (l 6) (l 17)) (l 17)) (s (l 6) (s (l 6) (l 17))))) (t (j (l 11) (s (s (l 6) (t (l 6) (l 12))) (l 12))) (s (l 17) (l 12)))) (s (l 17) (s (l 17) (l 12)))) (s (t (s (l 6) (j (s (l 6) (t (l 6) (l 12))) (l 12))) (s (j (t (s (l 6) (t (l 6) (l 17))) (l 17)) (s (l 18) (t (l 12) (l 18)))) (t (l 12) (t (l 12) (l 17))))) (t (l 12) (t (l 12) (l 17))))))) (t (s (s (s (s (l 18) (s (l 18) (s (l 18) (t (l 18) (j (t (l 18) (l 17)) (l 18)))))) (j (t (j (l 17) (l 18)) (l 17)) (s (l 18) (s (l 18) (s (l 18) (t (l 18) (j (l 17) (l 18)))))))) (j (l 17) (t (s (l 18) (j (s (s (l 18) (l 17)) (l 17)) (l 18))) (s (j (l 17) (s (s (l 18) (s (l 18) (j (l 17) (l 18)))) (t (l 18) (l 17)))) (l 17))))) (j (t (s (l 17) (t (l 12) (s (j (l 12) (l 17)) (q 12)))) (s (t (s (l 17) (j (s (l 17) (l 23)) (l 17))) (s (j (s (l 17) (l 23)) (l 17)) (q 17))) (q 17))) (s (s (s (t (t (j (l 17) (l 18)) (l 17)) (l 17)) (l 17)) (l 17)) (t (l 17) (q 17))))) (s (t (t (t (t (t (t (t (t (t (t (s (s (s (l 18) (l 16)) (l 16)) (s (l 16) (l 17))) (s (s (s (l 18) (l 16)) (l 16)) (s (l 16) (l 17)))) (s (s (s (l 18) (l 16)) (l 16)) (s (l 16) (l 17)))) (s (s (s (l 18) (l 16)) (l 16)) (s (l 16) (l 17)))) (s (l 16) (s (l 16) (l 17)))) (l 16)) (l 16)) (l 16)) (l 16)) (l 16)) (s (l 16) (q 16))) (q 17)))) (t (s (t (t (j (l 11) (t (s (l 11) (j (l 11) (t (l 11) (l 12)))) (s (j (l 11) (l 12)) (s (j (l 11) (l 12)) (l 12))))) (j (s (t (l 11) (j (l 11) (s (s (l 11) (l 12)) (l 12)))) (t (s (j (l 11) (l 12)) (s (j (l 11) (l 12)) (l 8))) (l 12))) (s (s (s (s (s (s (t (t (j (l 11) (l 12)) (l 12)) (l 12)) (l 12)) (l 12)) (l 12)) (l 12)) (l 12)) (l 12)))) (j (s (l 12) (t (l 12) (q 12))) (s (t (l 12) (s (l 17) (t (j (l 12) (l 17)) (q 17)))) (t (j (s (l 12) (t (l 12) (q 12))) (t (s (l 12) (s (l 12) (l 13))) (s (s (l 12) (l 13)) (q 13)))) (q 12))))) (t (t (s (s (s (s (s (s (s (s (s (s (t (t (l 11) (l 8)) (l 8)) (l 8)) (l 8)) (l 8)) (l 8)) (l 8)) (l 8)) (l 8)) (l 8)) (l 8)) (l 8)) (s (s (s (s (t (l 8) (l 12)) (l 8)) (l 8)) (l 8)) (q 8))) (q 12))) (s (s (s (s (s (s (s (s (s (s (s (t (t (t (t (t (t (t (t (t (t (t (j (q 12) (q 17)) (k)) (k)) (k)) (k)) (k)) (k)) (k)) (k)) (k)) (k)) (k)) (k)) (k)) (k)) (k)) (k)) (k)) (k)) (k)) (k)) (k)) (k)))

open Tr in
def trmm1 : Tr := t (s (t (t (s (s (l 0) (t (s (l 0) (j (l 7) (s (s (l 0) (s (l 0) (t (l 0) (j (l 7) (l 1))))) (t (l 1) (j (l 7) (l 1)))))) (t (s (l 0) (t (j (l 7) (j (l 7) (l 1))) (l 7))) (l 7)))) (j (l 7) (j (s (t (t (l 1) (l 7)) (l 7)) (s (t (l 12) (l 7)) (l 12))) (s (l 1) (s (l 1) (j (j (l 12) (l 1)) (l 1))))))) (s (s (j (t (t (l 0) (t (s (l 0) (s (l 0) (j (l 6) (l 7)))) (s (l 0) (j (l 6) (s (l 6) (l 7)))))) (s (l 6) (s (l 6) (j (l 6) (l 7))))) (s (t (l 0) (t (s (l 0) (l 7)) (s (j (l 6) (l 7)) (l 7)))) (l 7))) (s (j (j (j (l 6) (l 7)) (l 7)) (l 7)) (l 7))) (s (s (l 7) (j (l 7) (j (l 7) (j (l 7) (t (l 1) (s (l 7) (l 13))))))) (j (l 12) (j (s (l 7) (t (s (s (l 7) (s (l 7) (s (s (l 7) (t (l 12) (j (l 12) (l 13)))) (l 12)))) (l 12)) (j (s (l 7) (t (l 12) (l 13))) (l 13)))) (s (j (s (t (s (l 7) (s (l 7) (s (l 7) (s (l 7) (j (l 7) (l 13)))))) (l 13)) (j (t (l 7) (l 13)) (l 13))) (s (t (l 1) (l 13)) (l 13))) (l 13))))))) (s (j (s (s (l 6) (s (l 6) (t (l 6) (t (l 6) (t (s (l 6) (t (l 6) (s (l 6) (l 18)))) (s (t (s (l 6) (l 18)) (l 18)) (l 18))))))) (t (j (s (l 6) (t (l 6) (l 18))) (t (l 7) (t (l 7) (j (s (l 6) (l 18)) (l 7))))) (s (t (s (j (l 6) (j (l 6) (j (l 6) (l 7)))) (t (j (l 18) (j (l 18) (l 7))) (l 18))) (l 18)) (l 18)))) (t (s (s (s (j (l 6) (l 7)) (l 7)) (l 7)) (l 7)) (t (s (t (s (j (s (l 6) (l 7)) (l 7)) (l 7)) (l 19)) (l 7)) (s (l 19) (j (s (s (l 19) (s (l 19) (j (s (l 19) (l 18)) (l 19)))) (j (l 18) (t (l 7) (l 19)))) (l 19)))))) (j (s (t (t (j (s (j (s (l 6) (l 12)) (s (l 7) (l 12))) (l 12)) (l 7)) (t (t (j (s (l 18) (l 12)) (s (l 7) (l 18))) (l 18)) (l 18))) (l 18)) (j (t (l 12) (s (j (t (l 12) (s (j (l 17) (l 18)) (l 17))) (s (l 18) (s (l 18) (t (l 18) (l 13))))) (j (t (s (l 12) (t (l 12) (l 17))) (l 17)) (s (s (t (t (j (l 12) (l 18)) (l 13)) (l 13)) (l 13)) (l 13))))) (s (t (t (t (l 12) (l 18)) (l 18)) (l 18)) (t (t (t (l 12) (j (l 12) (l 13))) (s (l 18) (l 13))) (l 13))))) (s (t (s (s (l 7) (s (l 7) (s (l 7) (s (l 7) (s (l 7) (s (l 7) (s (l 7) (t (l 7) (j (l 7) (l 13)))))))))) (j (s (l 7) (s (l 7) (t (l 7) (t (l 7) (l 13))))) (s (j (l 7) (l 13)) (l 13)))) (j (s (t (j (l 18) (s (l 7) (s (l 7) (l 13)))) (l 18)) (l 18)) (s (s (l 19) (j (j (l 13) (l 19)) (l 19))) (j (l 13) (j (s (l 19) (l 13)) (l 19)))))) (s (s (t (t (j (l 7) (l 13)) (l 13)) (t (l 13) (l 18))) (t (s (s (t (j (t (l 7) (l 13)) (l 13)) (l 13)) (l 13)) (l 13)) (t (l 13) (l 18)))) (t (l 13) (t (l 13) (l 18)))))))) (t (s (j (t (l 12) (s (s (l 12) (s (l 12) (s (l 12) (s (l 12) (t (l 12) (j (l 12) (l 13))))))) (s (t (l 12) (j (l 12) (l 13))) (t (s (s (l 12) (s (t (l 12) (j (l 12) (l 13))) (t (l 12) (j (l 12) (l 13))))) (l 8)) (t (j (j (l 12) (l 13)) (l 13)) (l 13)))))) (t (j (s (l 12) (s (l 12) (t (l 12) (t (l 12) (l 13))))) (t (t (l 12) (j (l 12) (l 13))) (s (j (l 12) (l 13)) (l 13)))) (s (t (j (j (l 12) (l 13)) (l 13)) (l 13)) (l 13)))) (t (s (s (s (s (s (s (s (s (s (s (t (t (l 12) (l 8)) (l 8)) (l 8)) (l 8)) (l 8)) (l 8)) (l 8)) (l 8)) (l 8)) (l 8)) (l 8)) (l 8)) (s (s (s (s (s (t (l 8) (l 13)) (l 8)) (l 8)) (l 8)) (l 8)) (q 8)))) (s (j (s (t (j (t (l 12) (s (j (l 12) (s (l 12) (l 13))) (l 13))) (s (s (t (t (l 12) (l 13)) (l 13)) (l 13)) (l 13))) (l 13)) (t (l 13) (q 13))) (j (t (s (l 13) (s (l 13) (t (l 13) (q 13)))) (s (s (l 13) (t (l 13) (q 13))) (q 13))) (t (s (l 13) (t (s (l 13) (j (l 13) (l 14))) (s (j (l 13) (l 14)) (q 14)))) (s (l 18) (q 14))))) (q 13)))) (s (t (t (s (j (s (j (l 18) (s (l 19) (j (l 18) (l 19)))) (l 18)) (s (l 19) (j (s (j (l 18) (l 19)) (l 18)) (l 19)))) (j (s (s (l 18) (j (t (j (s (l 18) (l 17)) (l 18)) (l 17)) (l 18))) (j (l 17) (l 13))) (s (s (t (j (l 18) (j (l 18) (l 19))) (l 18)) (l 18)) (l 18)))) (s (j (s (s (j (l 18) (s (l 19) (l 18))) (l 18)) (s (l 18) (t (l 18) (j (j (l 17) (s (l 18) (l 17))) (l 18))))) (s (s (l 19) (s (l 19) (j (t (l 19) (l 18)) (l 19)))) (j (l 18) (s (t (l 19) (j (s (s (l 19) (l 18)) (l 18)) (t (l 19) (s (l 19) (l 18))))) (s (s (t (l 19) (l 18)) (l 18)) (l 18)))))) (s (j (j (l 17) (t (s (l 18) (s (l 18) (l 17))) (s (j (l 17) (l 18)) (q 17)))) (s (l 18) (t (l 18) (q 18)))) (s (s (s (s (s (s (s (s (s (t (t (t (t (t (t (t (t (t (j (q 17) (q 18)) (k)) (k)) (k)) (k)) (k)) (k)) (k)) (k)) (k)) (k)) (k)) (k)) (k)) (k)) (k)) (k)) (k)) (k))))) (s (t (t (t (t (t (t (t (t (t (t (s (s (s (s (s (s (s (l 19) (j (j (l 18) (l 19)) (l 19))) (s (s (s (s (j (j (l 18) (l 19)) (l 19)) (l 16)) (l 16)) (l 16)) (l 16))) (l 16)) (l 16)) (l 16)) (l 16)) (s (l 16) (s (l 16) (s (l 16) (j (l 17) (l 18)))))) (s (s (s (s (s (s (s (l 19) (j (j (l 18) (l 19)) (l 19))) (l 16)) (l 16)) (l 16)) (l 16)) (l 16)) (s (l 16) (s (l 16) (s (l 16) (j (l 17) (l 18))))))) (s (s (s (s (s (s (s (l 19) (j (j (l 18) (l 19)) (l 19))) (l 16)) (l 16)) (l 16)) (l 16)) (l 16)) (s (l 16) (s (l 16) (s (l 16) (j (l 17) (l 18))))))) (s (s (s (s (s (s (s (s (l 19) (t (l 19) (l 16))) (l 16)) (l 16)) (l 16)) (l 16)) (l 16)) (l 16)) (s (l 16) (s (l 16) (s (l 16) (j (l 17) (l 18))))))) (s (l 16) (s (l 16) (s (l 16) (s (l 16) (j (l 17) (l 18))))))) (l 16)) (l 16)) (l 16)) (l 16)) (l 16)) (s (l 16) (q 16))) (s (s (s (s (s (s (s (s (s (s (t (t (t (t (t (t (t (t (t (t (j (q 17) (q 18)) (k)) (k)) (k)) (k)) (k)) (k)) (k)) (k)) (k)) (k)) (k)) (k)) (k)) (k)) (k)) (k)) (k)) (k)) (k)) (k)))) (s (s (s (s (s (s (s (s (s (s (s (t (t (t (t (t (t (t (t (t (t (t (j (q 13) (q 18)) (k)) (k)) (k)) (k)) (k)) (k)) (k)) (k)) (k)) (k)) (k)) (k)) (k)) (k)) (k)) (k)) (k)) (k)) (k)) (k)) (k)) (k)))

open Tr in
def trmm2 : Tr := t (s (t (t (s (s (l 0) (t (s (l 0) (j (s (s (l 0) (l 1)) (l 1)) (s (s (l 0) (s (l 0) (l 2))) (l 2)))) (t (s (l 0) (j (l 1) (j (l 1) (l 2)))) (l 1)))) (j (l 1) (j (s (t (l 2) (l 1)) (s (j (l 13) (s (l 2) (j (l 13) (l 2)))) (l 13))) (l 2)))) (s (s (s (t (l 0) (j (l 7) (t (s (l 0) (l 1)) (l 1)))) (j (j (t (t (l 0) (l 7)) (l 7)) (s (t (l 0) (l 1)) (l 1))) (l 1))) (s (s (t (l 1) (j (j (l 7) (l 1)) (l 1))) (l 1)) (l 1))) (s (j (l 1) (j (l 1) (j (l 1) (t (l 2) (s (l 1) (l 14)))))) (j (s (j (l 13) (l 1)) (l 13)) (j (s (s (l 1) (s (l 1) (t (s (l 1) (s (l 1) (s (l 1) (j (l 1) (j (l 1) (l 14)))))) (j (l 1) (l 14))))) (t (j (l 13) (j (t (l 13) (l 14)) (l 14))) (l 14))) (s (s (t (t (l 2) (l 14)) (l 14)) (l 14)) (l 14))))))) (s (j (j (s (l 7) (t (s (l 7) (t (j (l 7) (l 1)) (s (l 7) (l 19)))) (l 19))) (s (s (l 7) (t (t (l 1) (l 7)) (j (s (l 7) (s (l 7) (t (l 7) (l 19)))) (t (s (l 7) (l 1)) (l 20))))) (t (l 1) (t (j (t (s (j (l 7) (l 1)) (l 19)) (s (s (s (l 7) (l 19)) (l 19)) (l 19))) (s (l 1) (t (l 1) (s (l 1) (l 19))))) (s (j (l 19) (s (l 20) (j (l 19) (l 20)))) (l 19)))))) (t (l 1) (t (l 1) (s (l 20) (s (l 20) (s (l 20) (j (j (l 19) (l 20)) (l 20)))))))) (j (s (t (j (t (j (s (s (l 7) (l 13)) (l 13)) (s (l 1) (l 13))) (l 19)) (t (l 1) (s (j (s (l 1) (l 19)) (l 1)) (s (t (l 1) (l 19)) (l 19))))) (l 19)) (j (t (t (l 13) (t (l 13) (t (l 13) (j (l 13) (s (l 19) (s (l 19) (l 14))))))) (s (j (s (s (l 19) (s (l 19) (s (l 19) (s (l 19) (s (l 19) (t (l 19) (t (l 19) (l 18)))))))) (t (j (l 13) (l 19)) (j (l 18) (s (l 19) (l 14))))) (l 19)) (j (t (j (l 13) (t (l 13) (l 14))) (l 18)) (l 14)))) (t (t (t (s (l 1) (j (l 13) (l 14))) (j (s (l 19) (l 13)) (j (l 19) (l 14)))) (l 19)) (l 19)))) (s (t (j (s (l 1) (s (l 1) (t (l 1) (l 14)))) (s (s (l 1) (t (l 1) (l 14))) (l 14))) (j (j (s (t (t (l 1) (l 19)) (l 19)) (l 19)) (s (s (t (l 1) (l 20)) (l 14)) (l 14))) (j (s (l 20) (t (l 14) (t (l 14) (l 19)))) (l 20)))) (t (s (s (s (s (s (s (t (j (l 1) (l 14)) (l 14)) (l 14)) (l 14)) (l 14)) (l 14)) (l 14)) (l 14)) (t (l 14) (l 19))))))) (t (s (j (t (l 13) (s (s (l 13) (t (l 13) (j (l 13) (t (l 13) (l 14))))) (j (s (l 13) (t (l 13) (s (t (l 13) (l 14)) (l 14)))) (t (s (t (l 13) (l 14)) (s (t (l 13) (l 14)) (l 14))) (l 14))))) (t (j (s (l 13) (t (l 13) (s (t (l 13) (l 14)) (s (l 14) (s (l 14) (l 8)))))) (t (j (s (l 13) (l 14)) (t (l 13) (l 14))) (l 14))) (s (s (s (s (t (t (j (l 13) (l 14)) (l 14)) (l 14)) (l 14)) (l 14)) (l 14)) (l 14)))) (t (s (s (s (s (s (s (s (s (s (s (t (t (l 13) (l 8)) (l 8)) (l 8)) (l 8)) (l 8)) (l 8)) (l 8)) (l 8)) (l 8)) (l 8)) (l 8)) (l 8)) (s (s (s (s (s (t (l 8) (s (s (l 14) (s (s (l 14) (t (l 14) (t (l 14) (t (l 14) (t (l 14) (t (l 14) (k))))))) (t (l 14) (t (l 14) (t (l 14) (t (l 8) (t (l 8) (k)))))))) (s (s (s (s (t (l 14) (t (l 14) (t (l 8) (t (l 8) (q 8))))) (l 8)) (l 8)) (l 8)) (l 8)))) (l 8)) (l 8)) (l 8)) (l 8)) (q 8)))) (s (j (s (t (j (t (s (l 13) (j (l 13) (l 14))) (j (s (l 13) (l 14)) (l 14))) (l 14)) (l 14)) (t (l 14) (q 14))) (s (t (l 14) (s (s (t (l 14) (l 19)) (l 19)) (t (j (l 14) (l 15)) (q 19)))) (t (j (s (l 14) (t (l 14) (q 14))) (s (t (l 14) (l 15)) (l 15))) (q 14)))) (q 14)))) (s (t (t (s (j (s (j (s (t (l 7) (l 19)) (l 19)) (s (l 20) (j (l 19) (l 20)))) (l 19)) (s (l 20) (s (l 20) (j (j (l 19) (s (l 20) (l 19))) (l 20))))) (s (s (t (j (l 19) (j (l 19) (j (l 19) (l 20)))) (l 19)) (t (l 19) (j (j (j (l 18) (l 19)) (l 19)) (l 19)))) (j (j (j (l 18) (l 14)) (t (l 14) (s (s (l 19) (l 14)) (q 14)))) (l 19)))) (s (j (s (s (j (l 19) (l 20)) (l 19)) (s (l 19) (t (l 19) (t (l 19) (j (j (l 18) (l 19)) (l 19)))))) (s (s (l 20) (s (l 20) (s (l 20) (t (l 20) (t (l 20) (l 16)))))) (j (s (s (t (l 20) (l 19)) (l 19)) (l 19)) (s (s (l 20) (j (t (l 20) (l 19)) (l 20))) (s (t (l 20) (l 19)) (l 19)))))) (s (j (j (s (s (t (l 19) (l 18)) (l 18)) (l 18)) (t (l 19) (s (s (l 19) (t (l 19) (q 19))) (q 19)))) (l 19)) (s (s (s (s (s (s (s (s (s (t (t (t (t (t (t (t (t (t (j (q 18) (q 19)) (k)) (k)) (k)) (k)) (k)) (k)) (k)) (k)) (k)) (k)) (k)) (k)) (k)) (k)) (k)) (k)) (k)) (k))))) (s (t (t (t (t (t (t (t (t (t (t (s (s (s (s (s (l 20) (l 16)) (l 16)) (l 16)) (l 16)) (s (l 16) (s (l 16) (s (l 16) (s (l 16) (j (j (l 18) (l 19)) (l 19))))))) (s (s (s (s (s (l 20) (l 16)) (l 16)) (l 16)) (l 16)) (s (l 16) (s (l 16) (s (l 16) (s (l 16) (s (l 16) (j (j (l 18) (l 19)) (l 19))))))))) (s (s (s (s (s (l 20) (l 16)) (l 16)) (l 16)) (l 16)) (s (l 16) (s (l 16) (s (l 16) (s (l 16) (s (l 16) (j (j (l 18) (l 19)) (l 19))))))))) (s (s (s (s (s (l 20) (l 16)) (l 16)) (l 16)) (l 16)) (s (l 16) (s (l 16) (s (l 16) (s (l 16) (s (l 16) (j (j (l 18) (l 19)) (l 19))))))))) (s (l 16) (s (l 16) (s (l 16) (s (l 16) (s (l 16) (s (l 16) (s (l 16) (q 16))))))))) (l 16)) (l 16)) (l 16)) (l 16)) (l 16)) (s (l 16) (q 16))) (s (s (s (s (s (s (s (s (s (s (t (t (t (t (t (t (t (t (t (t (j (j (q 18) (q 19)) (q 19)) (k)) (k)) (k)) (k)) (k)) (k)) (k)) (k)) (k)) (k)) (k)) (k)) (k)) (k)) (k)) (k)) (k)) (k)) (k)) (k)))) (s (s (s (s (s (s (s (s (s (s (s (t (t (t (t (t (t (t (t (t (t (t (j (q 14) (q 19)) (k)) (k)) (k)) (k)) (k)) (k)) (k)) (k)) (k)) (k)) (k)) (k)) (k)) (k)) (k)) (k)) (k)) (k)) (k)) (k)) (k)) (k)))

open Tr in
def trmm3 : Tr := t (s (t (s (s (t (l 0) (s (t (l 0) (t (s (l 0) (j (l 1) (l 2))) (j (l 1) (j (l 1) (l 2))))) (j (t (t (l 0) (j (l 1) (s (l 0) (l 2)))) (l 1)) (s (t (l 0) (l 2)) (l 2))))) (t (t (s (l 0) (t (j (l 2) (s (l 0) (j (l 2) (l 3)))) (l 2))) (s (s (l 0) (l 2)) (l 2))) (s (s (s (t (l 2) (j (t (l 2) (l 1)) (l 2))) (l 2)) (l 2)) (l 2)))) (s (t (t (t (j (l 2) (l 3)) (l 2)) (l 2)) (l 2)) (s (t (j (l 2) (t (t (l 3) (l 14)) (l 2))) (j (l 14) (l 2))) (t (j (l 2) (l 14)) (j (l 14) (j (s (l 2) (t (l 14) (t (l 14) (l 15)))) (t (t (l 14) (j (l 14) (l 15))) (l 15)))))))) (s (j (s (s (l 1) (s (l 1) (t (l 1) (t (l 1) (t (l 1) (l 20)))))) (t (j (s (l 1) (t (l 1) (s (l 1) (l 20)))) (s (s (l 1) (l 2)) (l 2))) (s (t (s (s (l 1) (t (l 1) (s (t (l 1) (l 20)) (l 20)))) (t (j (l 20) (j (l 20) (l 2))) (l 20))) (l 20)) (l 20)))) (t (s (s (s (l 1) (l 2)) (l 2)) (l 2)) (s (t (s (j (l 1) (l 2)) (l 2)) (l 21)) (t (s (l 2) (s (l 2) (s (l 2) (s (l 2) (s (l 2) (s (l 2) (s (l 2) (t (l 2) (j (l 20) (l 2)))))))))) (j (s (s (l 21) (j (l 20) (l 21))) (l 20)) (l 21)))))) (j (s (t (t (j (t (s (l 2) (l 14)) (s (j (l 20) (l 2)) (l 14))) (l 2)) (s (s (j (l 20) (t (l 2) (l 20))) (l 20)) (l 20))) (l 20)) (j (t (s (l 14) (s (l 14) (s (l 14) (s (l 14) (s (l 14) (s (l 14) (t (l 14) (t (l 14) (l 15))))))))) (s (s (l 20) (j (j (t (l 14) (l 19)) (l 20)) (l 20))) (s (t (j (t (l 14) (j (l 14) (l 15))) (l 15)) (l 15)) (l 15)))) (t (t (t (l 14) (j (l 14) (s (l 20) (l 15)))) (s (l 20) (l 15))) (s (l 20) (l 15))))) (s (t (s (l 2) (s (l 2) (s (l 2) (t (l 2) (t (l 2) (l 15)))))) (j (s (s (s (s (s (t (t (l 2) (l 20)) (l 20)) (l 20)) (l 20)) (l 20)) (l 20)) (l 20)) (s (t (s (l 2) (s (l 2) (l 15))) (l 20)) (l 15)))) (s (t (t (j (s (l 2) (s (l 2) (l 15))) (l 15)) (l 15)) (l 15)) (l 15)))))) (t (s (t (s (l 14) (s (l 14) (t (l 14) (s (t (l 14) (j (l 14) (l 15))) (t (s (l 14) (l 8)) (l 8)))))) (j (s (l 14) (t (s (l 14) (s (s (l 14) (s (l 14) (s (s (l 14) (t (l 14) (j (l 14) (l 15)))) (t (l 14) (j (l 14) (l 15)))))) (l 8))) (j (s (l 14) (s (t (l 14) (l 15)) (l 15))) (l 15)))) (s (t (j (l 14) (l 15)) (l 15)) (l 15)))) (t (s (s (s (s (s (s (s (s (s (s (t (l 14) (l 8)) (l 8)) (l 8)) (l 8)) (l 8)) (l 8)) (l 8)) (l 8)) (l 8)) (l 8)) (l 8)) (s (s (s (t (l 8) (l 15)) (l 8)) (l 8)) (q 8)))) (s (s (t (j (j (t (s (l 14) (s (l 14) (l 15))) (s (t (l 14) (l 15)) (l 15))) (l 15)) (l 15)) (s (l 15) (t (l 15) (q 15)))) (t (s (l 15) (t (l 15) (q 15))) (q 15))) (q 15)))) (s (t (s (s (j (s (j (s (j (l 20) (s (l 21) (l 20))) (l 20)) (s (l 21) (t (l 21) (l 20)))) (s (s (t (j (l 20) (l 21)) (l 20)) (l 20)) (l 20))) (s (l 21) (s (l 21) (t (l 21) (j (l 20) (l 21)))))) (s (t (j (l 20) (j (s (l 21) (l 20)) (l 21))) (l 20)) (s (l 20) (t (l 20) (t (l 20) (t (l 20) (t (s (l 20) (s (l 20) (s (l 20) (j (l 19) (l 20))))) (j (j (l 19) (l 20)) (l 20))))))))) (j (s (t (s (l 20) (s (l 20) (t (l 20) (j (l 19) (l 20))))) (j (s (s (t (l 20) (l 19)) (l 19)) (l 19)) (t (s (l 20) (s (l 20) (l 19))) (s (s (l 20) (l 19)) (q 20))))) (t (j (j (l 19) (l 15)) (l 15)) (q 19))) (s (s (l 20) (s (l 20) (s (l 20) (s (l 20) (t (l 20) (t (l 20) (k))))))) (t (s (l 20) (t (l 20) (q 20))) (q 20))))) (s (t (t (t (t (t (t (t (t (t (t (s (s (s (s (l 21) (l 16)) (l 16)) (l 16)) (s (l 20) (s (l 16) (s (l 16) (j (l 19) (l 20)))))) (s (s (s (s (l 21) (l 16)) (l 16)) (l 16)) (s (l 20) (s (l 16) (s (l 16) (j (l 19) (l 20))))))) (s (s (s (s (l 21) (l 16)) (l 16)) (l 16)) (s (l 20) (s (l 16) (s (l 16) (j (l 19) (l 20))))))) (s (s (s (s (l 21) (l 16)) (l 16)) (l 16)) (s (l 20) (s (l 16) (s (l 16) (j (l 19) (l 20))))))) (s (l 16) (s (l 16) (s (l 16) (s (l 16) (j (l 19) (l 20))))))) (l 16)) (l 16)) (l 16)) (l 16)) (l 16)) (s (l 16) (q 16))) (s (s (s (s (s (s (s (s (s (s (t (t (t (t (t (t (t (t (t (t (j (q 19) (q 20)) (k)) (k)) (k)) (k)) (k)) (k)) (k)) (k)) (k)) (k)) (k)) (k)) (k)) (k)) (k)) (k)) (k)) (k)) (k)) (k)))) (q 15))

theorem c_pp0 : chk (1) (1) trpp0 0 4096 0 4096 (-64) (-32) = true := by decide +kernel
theorem c_pp1 : chk (1) (1) trpp1 0 4096 0 4096 (-32) (0) = true := by decide +kernel
theorem c_pp2 : chk (1) (1) trpp2 0 4096 0 4096 (0) (32) = true := by decide +kernel
theorem c_pp3 : chk (1) (1) trpp3 0 4096 0 4096 (32) (64) = true := by decide +kernel
theorem c_pm0 : chk (1) (-1) trpm0 0 4096 0 4096 (-64) (-32) = true := by decide +kernel
theorem c_pm1 : chk (1) (-1) trpm1 0 4096 0 4096 (-32) (0) = true := by decide +kernel
theorem c_pm2 : chk (1) (-1) trpm2 0 4096 0 4096 (0) (32) = true := by decide +kernel
theorem c_pm3 : chk (1) (-1) trpm3 0 4096 0 4096 (32) (64) = true := by decide +kernel
theorem c_mp0 : chk (-1) (1) trmp0 0 4096 0 4096 (-64) (-32) = true := by decide +kernel
theorem c_mp1 : chk (-1) (1) trmp1 0 4096 0 4096 (-32) (0) = true := by decide +kernel
theorem c_mp2 : chk (-1) (1) trmp2 0 4096 0 4096 (0) (32) = true := by decide +kernel
theorem c_mp3 : chk (-1) (1) trmp3 0 4096 0 4096 (32) (64) = true := by decide +kernel
theorem c_mm0 : chk (-1) (-1) trmm0 0 4096 0 4096 (-64) (-32) = true := by decide +kernel
theorem c_mm1 : chk (-1) (-1) trmm1 0 4096 0 4096 (-32) (0) = true := by decide +kernel
theorem c_mm2 : chk (-1) (-1) trmm2 0 4096 0 4096 (0) (32) = true := by decide +kernel
theorem c_mm3 : chk (-1) (-1) trmm3 0 4096 0 4096 (32) (64) = true := by decide +kernel

noncomputable def Dr (σ α β u v κ1 κ2 : ℝ) : ℝ :=
  4 * α ^ 2 + 4 * α * β + 65 / 16 * β ^ 2 - 4 * α * (κ1 * u + κ2 * v)
    - 2 * β * ((κ1 * u + κ2 * v) + 7 / 4 * σ * (κ2 * u - κ1 * v)) + κ1 ^ 2 + κ2 ^ 2

noncomputable def G (σ ε α β κ1 κ2 pu pv pw : ℝ) : ℝ :=
  (4 * α ^ 2 + 4 * α * β + 65 / 16 * β ^ 2 + κ1 ^ 2 + κ2 ^ 2 - 1 / 4) * pw
    + ε * ((-4 * α * κ1 - 2 * β * (κ1 + 7 / 4 * σ * κ2)) * pu
      + (-4 * α * κ2 - 2 * β * (κ2 - 7 / 4 * σ * κ1)) * pv)

lemma Dz_G (sg ep A B PU PV PW k1 k2 : ℤ) :
    ((Dz sg A B (ep * PU) (ep * PV) PW k1 k2 : ℤ) : ℝ) - 671088640000 * (PW : ℝ)
      = 2684354560000 * G sg ep ((A : ℝ) / 4096) ((B : ℝ) / 4096) ((k1 : ℝ) / 100) ((k2 : ℝ) / 100)
        PU PV PW := by
  unfold Dz G
  push_cast
  ring

lemma ok1_G (sg ep A B PU PV PW k1 k2 : ℤ) (h : ok1 sg A B (ep * PU) (ep * PV) PW k1 k2 = true) :
    G sg ep ((A : ℝ) / 4096) ((B : ℝ) / 4096) ((k1 : ℝ) / 100) ((k2 : ℝ) / 100) PU PV PW < 0 := by
  unfold ok1 at h
  have h1 : Dz sg A B (ep * PU) (ep * PV) PW k1 k2 < 671088640000 * PW := of_decide_eq_true h
  have h2 : ((Dz sg A B (ep * PU) (ep * PV) PW k1 k2 : ℤ) : ℝ) < 671088640000 * (PW : ℝ) := by
    exact_mod_cast h1
  have h3 := Dz_G sg ep A B PU PV PW k1 k2
  linarith

lemma G_hom (σ ε α β κ1 κ2 pu pv pw c : ℝ) :
    G σ ε α β κ1 κ2 (c * pu) (c * pv) (c * pw) = c * G σ ε α β κ1 κ2 pu pv pw := by
  unfold G
  ring

lemma G_tri (σ ε α β κ1 κ2 a b x : ℝ) (hab : a < b) (_hab1 : 0 < 1 + a * b) (hxa : a ≤ x)
    (hxb : x ≤ b) (ha : G σ ε α β κ1 κ2 (1 - a ^ 2) (2 * a) (1 + a ^ 2) < 0)
    (hb : G σ ε α β κ1 κ2 (1 - b ^ 2) (2 * b) (1 + b ^ 2) < 0)
    (hT : G σ ε α β κ1 κ2 (1 - a * b) (a + b) (1 + a * b) < 0) :
    G σ ε α β κ1 κ2 (1 - x ^ 2) (2 * x) (1 + x ^ 2) < 0 := by
  have key : (b - a) ^ 2 * G σ ε α β κ1 κ2 (1 - x ^ 2) (2 * x) (1 + x ^ 2)
      = (b - x) ^ 2 * G σ ε α β κ1 κ2 (1 - a ^ 2) (2 * a) (1 + a ^ 2)
        + (x - a) ^ 2 * G σ ε α β κ1 κ2 (1 - b ^ 2) (2 * b) (1 + b ^ 2)
        + 2 * (x - a) * (b - x) * G σ ε α β κ1 κ2 (1 - a * b) (a + b) (1 + a * b) := by
    unfold G
    ring
  have hba : 0 < (b - a) ^ 2 := by nlinarith
  have e1 : (b - x) ^ 2 * G σ ε α β κ1 κ2 (1 - a ^ 2) (2 * a) (1 + a ^ 2) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos (sq_nonneg _) ha.le
  have e2 : (x - a) ^ 2 * G σ ε α β κ1 κ2 (1 - b ^ 2) (2 * b) (1 + b ^ 2) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos (sq_nonneg _) hb.le
  have e3 : 2 * (x - a) * (b - x) * G σ ε α β κ1 κ2 (1 - a * b) (a + b) (1 + a * b) ≤ 0 := by
    apply mul_nonpos_of_nonneg_of_nonpos _ hT.le
    have : 0 ≤ (x - a) * (b - x) := mul_nonneg (by linarith) (by linarith)
    linarith
  have hpos : 0 < (b - x) ^ 2 + (x - a) ^ 2 := by
    rcases lt_or_ge x b with h | h
    · nlinarith
    · nlinarith
  have e4 : (b - x) ^ 2 * G σ ε α β κ1 κ2 (1 - a ^ 2) (2 * a) (1 + a ^ 2)
      + (x - a) ^ 2 * G σ ε α β κ1 κ2 (1 - b ^ 2) (2 * b) (1 + b ^ 2) < 0 := by
    rcases lt_or_ge x b with h | h
    · have : 0 < (b - x) ^ 2 := by nlinarith
      have := mul_neg_of_pos_of_neg this ha
      linarith
    · have : 0 < (x - a) ^ 2 := by nlinarith
      have := mul_neg_of_pos_of_neg this hb
      linarith
  by_contra hc
  rw [not_lt] at hc
  have := mul_nonneg hba.le hc
  linarith

lemma G_Dr (σ ε α β κ1 κ2 x : ℝ) :
    (1 + x ^ 2) * (Dr σ α β (ε * ((1 - x ^ 2) / (1 + x ^ 2))) (ε * (2 * x / (1 + x ^ 2))) κ1 κ2 - 1 / 4)
      = G σ ε α β κ1 κ2 (1 - x ^ 2) (2 * x) (1 + x ^ 2) := by
  have h : (1 + x ^ 2) ≠ 0 := by positivity
  unfold Dr G
  field_simp
  ring

lemma stepA (σ α0 α1 α β u v κ1 κ2 M : ℝ) (h0 : Dr σ α0 β u v κ1 κ2 < M)
    (h1 : Dr σ α1 β u v κ1 κ2 < M) (ha0 : α0 ≤ α) (ha1 : α ≤ α1) : Dr σ α β u v κ1 κ2 < M := by
  have key : (α1 - α0) * (Dr σ α β u v κ1 κ2 - M) = (α1 - α) * (Dr σ α0 β u v κ1 κ2 - M)
      + (α - α0) * (Dr σ α1 β u v κ1 κ2 - M) - 4 * (α1 - α0) * (α - α0) * (α1 - α) := by
    unfold Dr
    ring
  rcases eq_or_lt_of_le (le_trans ha0 ha1) with he | hlt
  · have e1 : α = α0 := by linarith
    rw [e1]; exact h0
  · have p1 : 0 ≤ (α1 - α) * (M - Dr σ α0 β u v κ1 κ2) := mul_nonneg (by linarith) (by linarith)
    have p2 : 0 ≤ (α - α0) * (M - Dr σ α1 β u v κ1 κ2) := mul_nonneg (by linarith) (by linarith)
    have p3 : 0 ≤ (α1 - α0) * (α - α0) * (α1 - α) :=
      mul_nonneg (mul_nonneg (by linarith) (by linarith)) (by linarith)
    have p4 : 0 < (α1 - α) * (M - Dr σ α0 β u v κ1 κ2) + (α - α0) * (M - Dr σ α1 β u v κ1 κ2) := by
      rcases lt_or_ge α α1 with h | h
      · have := mul_pos (sub_pos.2 h) (sub_pos.2 h0); linarith
      · have := mul_pos (show (0:ℝ) < α - α0 by linarith) (sub_pos.2 h1); linarith
    by_contra hc
    rw [not_lt] at hc
    have := mul_nonneg (sub_pos.2 hlt).le (sub_nonneg.2 hc)
    linarith

lemma stepB (σ α β0 β1 β u v κ1 κ2 M : ℝ) (h0 : Dr σ α β0 u v κ1 κ2 < M)
    (h1 : Dr σ α β1 u v κ1 κ2 < M) (hb0 : β0 ≤ β) (hb1 : β ≤ β1) : Dr σ α β u v κ1 κ2 < M := by
  have key : (β1 - β0) * (Dr σ α β u v κ1 κ2 - M) = (β1 - β) * (Dr σ α β0 u v κ1 κ2 - M)
      + (β - β0) * (Dr σ α β1 u v κ1 κ2 - M) - 65 / 16 * (β1 - β0) * (β - β0) * (β1 - β) := by
    unfold Dr
    ring
  rcases eq_or_lt_of_le (le_trans hb0 hb1) with he | hlt
  · have e1 : β = β0 := by linarith
    rw [e1]; exact h0
  · have p1 : 0 ≤ (β1 - β) * (M - Dr σ α β0 u v κ1 κ2) := mul_nonneg (by linarith) (by linarith)
    have p2 : 0 ≤ (β - β0) * (M - Dr σ α β1 u v κ1 κ2) := mul_nonneg (by linarith) (by linarith)
    have p3 : 0 ≤ (β1 - β0) * (β - β0) * (β1 - β) :=
      mul_nonneg (mul_nonneg (by linarith) (by linarith)) (by linarith)
    have p4 : 0 < (β1 - β) * (M - Dr σ α β0 u v κ1 κ2) + (β - β0) * (M - Dr σ α β1 u v κ1 κ2) := by
      rcases lt_or_ge β β1 with h | h
      · have := mul_pos (sub_pos.2 h) (sub_pos.2 h0); linarith
      · have := mul_pos (show (0:ℝ) < β - β0 by linarith) (sub_pos.2 h1); linarith
    by_contra hc
    rw [not_lt] at hc
    have := mul_nonneg (sub_pos.2 hlt).le (sub_nonneg.2 hc)
    linarith

lemma corner (sg ep : ℤ) (c : ℕ) (S T j0 j1 : ℤ) (h : okc sg ep c S T j0 j1 = true)
    (hj : j0 < j1) (hj1 : 0 < 4096 + j0 * j1) (x : ℝ) (hx0 : (j0 : ℝ) / 64 ≤ x)
    (hx1 : x ≤ (j1 : ℝ) / 64) :
    Dr sg ((amn (c / 8) : ℝ) - (S : ℝ) / 4096) ((bmn (c / 8) : ℝ) - (T : ℝ) / 4096)
      (ep * ((1 - x ^ 2) / (1 + x ^ 2))) (ep * (2 * x / (1 + x ^ 2)))
      ((kxn (c % 8) : ℝ) / 100) ((kyn (c % 8) : ℝ) / 100) < 1 / 4 := by
  unfold okc at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨h1, h2⟩, h3⟩ := h
  have g1 := ok1_G _ _ _ _ _ _ _ _ _ h1
  have g2 := ok1_G _ _ _ _ _ _ _ _ _ h2
  have g3 := ok1_G _ _ _ _ _ _ _ _ _ h3
  set α : ℝ := (amn (c / 8) : ℝ) - (S : ℝ) / 4096 with hα
  set β : ℝ := (bmn (c / 8) : ℝ) - (T : ℝ) / 4096 with hβ
  have eA : (((amn (c / 8) * 4096 - S : ℤ) : ℝ) / 4096) = α := by rw [hα]; push_cast; ring
  have eB : (((bmn (c / 8) * 4096 - T : ℤ) : ℝ) / 4096) = β := by rw [hβ]; push_cast; ring
  rw [eA, eB] at g1 g2 g3
  set a : ℝ := (j0 : ℝ) / 64 with ha
  set b : ℝ := (j1 : ℝ) / 64 with hb
  have q1 : (((4096 - j0 * j0 : ℤ) : ℝ)) = 4096 * (1 - a ^ 2) := by rw [ha]; push_cast; ring
  have q2 : (((128 * j0 : ℤ) : ℝ)) = 4096 * (2 * a) := by rw [ha]; push_cast; ring
  have q3 : (((4096 + j0 * j0 : ℤ) : ℝ)) = 4096 * (1 + a ^ 2) := by rw [ha]; push_cast; ring
  have r1 : (((4096 - j1 * j1 : ℤ) : ℝ)) = 4096 * (1 - b ^ 2) := by rw [hb]; push_cast; ring
  have r2 : (((128 * j1 : ℤ) : ℝ)) = 4096 * (2 * b) := by rw [hb]; push_cast; ring
  have r3 : (((4096 + j1 * j1 : ℤ) : ℝ)) = 4096 * (1 + b ^ 2) := by rw [hb]; push_cast; ring
  have t1 : (((4096 - j0 * j1 : ℤ) : ℝ)) = 4096 * (1 - a * b) := by rw [ha, hb]; push_cast; ring
  have t2 : (((64 * (j0 + j1) : ℤ) : ℝ)) = 4096 * (a + b) := by rw [ha, hb]; push_cast; ring
  have t3 : (((4096 + j0 * j1 : ℤ) : ℝ)) = 4096 * (1 + a * b) := by rw [ha, hb]; push_cast; ring
  rw [q1, q2, q3, G_hom] at g1
  rw [r1, r2, r3, G_hom] at g2
  rw [t1, t2, t3, G_hom] at g3
  have hab : a < b := by
    rw [ha, hb]
    have : (j0 : ℝ) < j1 := by exact_mod_cast hj
    linarith
  have hab1 : 0 < 1 + a * b := by
    have : (0 : ℝ) < 4096 + (j0 : ℝ) * j1 := by exact_mod_cast hj1
    rw [ha, hb]
    nlinarith
  have gx := G_tri (sg : ℝ) (ep : ℝ) α β ((kxn (c % 8) : ℝ) / 100) ((kyn (c % 8) : ℝ) / 100) a b x
    hab hab1 hx0 hx1 (by nlinarith) (by nlinarith) (by nlinarith)
  have e := G_Dr (sg : ℝ) (ep : ℝ) α β ((kxn (c % 8) : ℝ) / 100) ((kyn (c % 8) : ℝ) / 100) x
  rw [← e] at gx
  have hx2 : 0 < 1 + x ^ 2 := by positivity
  by_contra hc
  rw [not_lt] at hc
  have := mul_nonneg hx2.le (sub_nonneg.2 hc)
  linarith

lemma leaf_sound (sg ep : ℤ) (c : ℕ) (S0 S1 T0 T1 j0 j1 : ℤ)
    (h : leafok sg ep c S0 S1 T0 T1 j0 j1 = true) (s t x : ℝ) (hs0 : (S0 : ℝ) / 4096 ≤ s)
    (hs1 : s ≤ (S1 : ℝ) / 4096) (ht0 : (T0 : ℝ) / 4096 ≤ t) (ht1 : t ≤ (T1 : ℝ) / 4096)
    (hx0 : (j0 : ℝ) / 64 ≤ x) (hx1 : x ≤ (j1 : ℝ) / 64) :
    Dr sg ((amn (c / 8) : ℝ) - s) ((bmn (c / 8) : ℝ) - t)
      (ep * ((1 - x ^ 2) / (1 + x ^ 2))) (ep * (2 * x / (1 + x ^ 2)))
      ((kxn (c % 8) : ℝ) / 100) ((kyn (c % 8) : ℝ) / 100) < 1 / 4 := by
  unfold leafok at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨hj, _⟩, _⟩, hj1⟩, c00⟩, c01⟩, c10⟩, c11⟩ := h
  have d00 := corner sg ep c S0 T0 j0 j1 c00 hj hj1 x hx0 hx1
  have d01 := corner sg ep c S0 T1 j0 j1 c01 hj hj1 x hx0 hx1
  have d10 := corner sg ep c S1 T0 j0 j1 c10 hj hj1 x hx0 hx1
  have d11 := corner sg ep c S1 T1 j0 j1 c11 hj hj1 x hx0 hx1
  have b0 := stepB _ _ _ _ _ _ _ _ _ _ d01 d00 (show (bmn (c / 8) : ℝ) - (T1 : ℝ) / 4096
    ≤ (bmn (c / 8) : ℝ) - t by linarith) (show (bmn (c / 8) : ℝ) - t
    ≤ (bmn (c / 8) : ℝ) - (T0 : ℝ) / 4096 by linarith)
  have b1 := stepB _ _ _ _ _ _ _ _ _ _ d11 d10 (show (bmn (c / 8) : ℝ) - (T1 : ℝ) / 4096
    ≤ (bmn (c / 8) : ℝ) - t by linarith) (show (bmn (c / 8) : ℝ) - t
    ≤ (bmn (c / 8) : ℝ) - (T0 : ℝ) / 4096 by linarith)
  exact stepA _ _ _ _ _ _ _ _ _ _ b1 b0 (by linarith) (by linarith)

lemma chk_sound (sg ep : ℤ) (tr : Tr) : ∀ (S0 S1 T0 T1 j0 j1 : ℤ),
    chk sg ep tr S0 S1 T0 T1 j0 j1 = true → ∀ s t x : ℝ, (S0 : ℝ) / 4096 ≤ s →
    s ≤ (S1 : ℝ) / 4096 → (T0 : ℝ) / 4096 ≤ t → t ≤ (T1 : ℝ) / 4096 → (j0 : ℝ) / 64 ≤ x →
    x ≤ (j1 : ℝ) / 64 → s + t ≤ 1 → ∃ c : ℕ, Dr sg ((amn (c / 8) : ℝ) - s) ((bmn (c / 8) : ℝ) - t)
      (ep * ((1 - x ^ 2) / (1 + x ^ 2))) (ep * (2 * x / (1 + x ^ 2)))
      ((kxn (c % 8) : ℝ) / 100) ((kyn (c % 8) : ℝ) / 100) < 1 / 4 := by
  induction tr with
  | l c =>
    intro S0 S1 T0 T1 j0 j1 h s t x hs0 hs1 ht0 ht1 hx0 hx1 _
    exact ⟨c, leaf_sound sg ep c S0 S1 T0 T1 j0 j1 h s t x hs0 hs1 ht0 ht1 hx0 hx1⟩
  | q c =>
    intro S0 S1 T0 T1 j0 j1 h s t x hs0 _ ht0 _ hx0 hx1 hst
    simp only [chk, Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨hq, h⟩ := h
    have hq' : (4096 : ℝ) ≤ (S0 : ℝ) + T0 := by exact_mod_cast hq
    exact ⟨c, leaf_sound sg ep c S0 S0 T0 T0 j0 j1 h s t x hs0 (by linarith) ht0 (by linarith)
      hx0 hx1⟩
  | k =>
    intro S0 S1 T0 T1 j0 j1 h s t x hs0 _ ht0 _ _ _ hst
    simp only [chk, decide_eq_true_eq] at h
    have hq' : (4096 : ℝ) < (S0 : ℝ) + T0 := by exact_mod_cast h
    exfalso
    linarith
  | s a b iha ihb =>
    intro S0 S1 T0 T1 j0 j1 h s t x hs0 hs1 ht0 ht1 hx0 hx1 hst
    simp only [chk, Bool.and_eq_true] at h
    rcases le_total s ((((S0 + S1) / 2 : ℤ) : ℝ) / 4096) with hm | hm
    · exact iha _ _ _ _ _ _ h.1 s t x hs0 hm ht0 ht1 hx0 hx1 hst
    · exact ihb _ _ _ _ _ _ h.2 s t x hm hs1 ht0 ht1 hx0 hx1 hst
  | t a b iha ihb =>
    intro S0 S1 T0 T1 j0 j1 h s t x hs0 hs1 ht0 ht1 hx0 hx1 hst
    simp only [chk, Bool.and_eq_true] at h
    rcases le_total t ((((T0 + T1) / 2 : ℤ) : ℝ) / 4096) with hm | hm
    · exact iha _ _ _ _ _ _ h.1 s t x hs0 hs1 ht0 hm hx0 hx1 hst
    · exact ihb _ _ _ _ _ _ h.2 s t x hs0 hs1 hm ht1 hx0 hx1 hst
  | j a b iha ihb =>
    intro S0 S1 T0 T1 j0 j1 h s t x hs0 hs1 ht0 ht1 hx0 hx1 hst
    simp only [chk, Bool.and_eq_true] at h
    rcases le_total x ((((j0 + j1) / 2 : ℤ) : ℝ) / 64) with hm | hm
    · exact iha _ _ _ _ _ _ h.1 s t x hs0 hs1 ht0 ht1 hx0 hm hst
    · exact ihb _ _ _ _ _ _ h.2 s t x hs0 hs1 ht0 ht1 hm hx1 hst

lemma chart0 (u v : ℝ) (h : u ^ 2 + v ^ 2 = 1) (hu : 0 ≤ u) : ∃ x : ℝ, -1 ≤ x ∧ x ≤ 1 ∧
    u = (1 - x ^ 2) / (1 + x ^ 2) ∧ v = 2 * x / (1 + x ^ 2) := by
  have h1 : 0 < 1 + u := by linarith
  refine ⟨v / (1 + u), ?_, ?_, ?_, ?_⟩
  · rw [le_div_iff₀ h1]; nlinarith
  · rw [div_le_iff₀ h1]; nlinarith
  · rw [eq_div_iff (by positivity)]
    field_simp
    linear_combination (1 + u) * h
  · rw [eq_div_iff (by positivity)]
    field_simp
    linear_combination v * h

lemma chart (u v : ℝ) (h : u ^ 2 + v ^ 2 = 1) : ∃ ep : ℤ, (ep = 1 ∨ ep = -1) ∧ ∃ x : ℝ,
    -1 ≤ x ∧ x ≤ 1 ∧ u = (ep : ℝ) * ((1 - x ^ 2) / (1 + x ^ 2)) ∧
      v = (ep : ℝ) * (2 * x / (1 + x ^ 2)) := by
  rcases le_total 0 u with hu | hu
  · obtain ⟨x, h1, h2, h3, h4⟩ := chart0 u v h hu
    exact ⟨1, Or.inl rfl, x, h1, h2, by rw [h3]; push_cast; ring, by rw [h4]; push_cast; ring⟩
  · obtain ⟨x, h1, h2, h3, h4⟩ := chart0 (-u) (-v) (by linear_combination h) (by linarith)
    exact ⟨-1, Or.inr rfl, x, h1, h2, by push_cast; linarith, by push_cast; linarith⟩

lemma geo (sg : ℤ) (hsg : sg = 1 ∨ sg = -1) (u v s t : ℝ) (huv : u ^ 2 + v ^ 2 = 1)
    (hs : 0 ≤ s) (ht : 0 ≤ t) (hst : s + t ≤ 1) : ∃ c : ℕ,
      Dr sg ((amn (c / 8) : ℝ) - s) ((bmn (c / 8) : ℝ) - t) u v
        ((kxn (c % 8) : ℝ) / 100) ((kyn (c % 8) : ℝ) / 100) < 1 / 4 := by
  obtain ⟨ep, hep, x, hx0, hx1, hu, hv⟩ := chart u v huv
  rw [hu, hv]
  rcases hsg with rfl | rfl <;> rcases hep with rfl | rfl
  · rcases le_total x (-1 / 2) with h1 | h1
    · exact chk_sound _ _ trpp0 0 4096 0 4096 (-64) (-32) c_pp0 s t x (by norm_num <;> linarith)
        (by norm_num <;> linarith) (by norm_num <;> linarith) (by norm_num <;> linarith)
        (by norm_num <;> linarith) (by norm_num <;> linarith) hst
    rcases le_total x 0 with h2 | h2
    · exact chk_sound _ _ trpp1 0 4096 0 4096 (-32) (0) c_pp1 s t x (by norm_num <;> linarith)
        (by norm_num <;> linarith) (by norm_num <;> linarith) (by norm_num <;> linarith)
        (by norm_num <;> linarith) (by norm_num <;> linarith) hst
    rcases le_total x (1 / 2) with h3 | h3
    · exact chk_sound _ _ trpp2 0 4096 0 4096 (0) (32) c_pp2 s t x (by norm_num <;> linarith)
        (by norm_num <;> linarith) (by norm_num <;> linarith) (by norm_num <;> linarith)
        (by norm_num <;> linarith) (by norm_num <;> linarith) hst
    · exact chk_sound _ _ trpp3 0 4096 0 4096 (32) (64) c_pp3 s t x (by norm_num <;> linarith)
        (by norm_num <;> linarith) (by norm_num <;> linarith) (by norm_num <;> linarith)
        (by norm_num <;> linarith) (by norm_num <;> linarith) hst
  · rcases le_total x (-1 / 2) with h1 | h1
    · exact chk_sound _ _ trpm0 0 4096 0 4096 (-64) (-32) c_pm0 s t x (by norm_num <;> linarith)
        (by norm_num <;> linarith) (by norm_num <;> linarith) (by norm_num <;> linarith)
        (by norm_num <;> linarith) (by norm_num <;> linarith) hst
    rcases le_total x 0 with h2 | h2
    · exact chk_sound _ _ trpm1 0 4096 0 4096 (-32) (0) c_pm1 s t x (by norm_num <;> linarith)
        (by norm_num <;> linarith) (by norm_num <;> linarith) (by norm_num <;> linarith)
        (by norm_num <;> linarith) (by norm_num <;> linarith) hst
    rcases le_total x (1 / 2) with h3 | h3
    · exact chk_sound _ _ trpm2 0 4096 0 4096 (0) (32) c_pm2 s t x (by norm_num <;> linarith)
        (by norm_num <;> linarith) (by norm_num <;> linarith) (by norm_num <;> linarith)
        (by norm_num <;> linarith) (by norm_num <;> linarith) hst
    · exact chk_sound _ _ trpm3 0 4096 0 4096 (32) (64) c_pm3 s t x (by norm_num <;> linarith)
        (by norm_num <;> linarith) (by norm_num <;> linarith) (by norm_num <;> linarith)
        (by norm_num <;> linarith) (by norm_num <;> linarith) hst
  · rcases le_total x (-1 / 2) with h1 | h1
    · exact chk_sound _ _ trmp0 0 4096 0 4096 (-64) (-32) c_mp0 s t x (by norm_num <;> linarith)
        (by norm_num <;> linarith) (by norm_num <;> linarith) (by norm_num <;> linarith)
        (by norm_num <;> linarith) (by norm_num <;> linarith) hst
    rcases le_total x 0 with h2 | h2
    · exact chk_sound _ _ trmp1 0 4096 0 4096 (-32) (0) c_mp1 s t x (by norm_num <;> linarith)
        (by norm_num <;> linarith) (by norm_num <;> linarith) (by norm_num <;> linarith)
        (by norm_num <;> linarith) (by norm_num <;> linarith) hst
    rcases le_total x (1 / 2) with h3 | h3
    · exact chk_sound _ _ trmp2 0 4096 0 4096 (0) (32) c_mp2 s t x (by norm_num <;> linarith)
        (by norm_num <;> linarith) (by norm_num <;> linarith) (by norm_num <;> linarith)
        (by norm_num <;> linarith) (by norm_num <;> linarith) hst
    · exact chk_sound _ _ trmp3 0 4096 0 4096 (32) (64) c_mp3 s t x (by norm_num <;> linarith)
        (by norm_num <;> linarith) (by norm_num <;> linarith) (by norm_num <;> linarith)
        (by norm_num <;> linarith) (by norm_num <;> linarith) hst
  · rcases le_total x (-1 / 2) with h1 | h1
    · exact chk_sound _ _ trmm0 0 4096 0 4096 (-64) (-32) c_mm0 s t x (by norm_num <;> linarith)
        (by norm_num <;> linarith) (by norm_num <;> linarith) (by norm_num <;> linarith)
        (by norm_num <;> linarith) (by norm_num <;> linarith) hst
    rcases le_total x 0 with h2 | h2
    · exact chk_sound _ _ trmm1 0 4096 0 4096 (-32) (0) c_mm1 s t x (by norm_num <;> linarith)
        (by norm_num <;> linarith) (by norm_num <;> linarith) (by norm_num <;> linarith)
        (by norm_num <;> linarith) (by norm_num <;> linarith) hst
    rcases le_total x (1 / 2) with h3 | h3
    · exact chk_sound _ _ trmm2 0 4096 0 4096 (0) (32) c_mm2 s t x (by norm_num <;> linarith)
        (by norm_num <;> linarith) (by norm_num <;> linarith) (by norm_num <;> linarith)
        (by norm_num <;> linarith) (by norm_num <;> linarith) hst
    · exact chk_sound _ _ trmm3 0 4096 0 4096 (32) (64) c_mm3 s t x (by norm_num <;> linarith)
        (by norm_num <;> linarith) (by norm_num <;> linarith) (by norm_num <;> linarith)
        (by norm_num <;> linarith) (by norm_num <;> linarith) hst

lemma sign_lemma {ι : Type*} (C C' : ι → ℝ) (hC : ∀ i j, C i * C j = C' i * C' j) :
    ∃ σ : ℝ, σ ^ 2 = 1 ∧ ∀ i, C i = σ * C' i := by
  by_cases h : ∀ i, C' i = 0
  · refine ⟨1, by norm_num, fun i => ?_⟩
    have := hC i i
    rw [h i] at this ⊢
    have h2 : C i ^ 2 = 0 := by nlinarith
    simpa using h2
  · simp only [not_forall] at h
    obtain ⟨r, hr⟩ := h
    have hrr := hC r r
    refine ⟨C r / C' r, ?_, fun i => ?_⟩
    · rw [div_pow, div_eq_one_iff_eq (pow_ne_zero 2 hr)]
      linear_combination hrr
    · have hir := hC i r
      have hz : C' r * (C i * C' r - C r * C' i) = 0 := by
        linear_combination (-C i) * hrr + C r * hir
      rcases mul_eq_zero.mp hz with h0 | h0
      · exact absurd h0 hr
      · rw [div_mul_eq_mul_div, eq_div_iff hr]
        linear_combination h0

lemma alg_step (D1 D2 P1 P2 Q1 Q2 w1 w2 W1 W2 σ k0x k0y kix kiy lx ly pix piy : ℝ)
    (hs : w1 ^ 2 + w2 ^ 2 = W1 ^ 2 + W2 ^ 2) (hne : W1 ^ 2 + W2 ^ 2 ≠ 0) (hσ2 : σ ^ 2 = 1)
    (hA : P1 * w1 + P2 * w2 = Q1 * W1 + Q2 * W2) (hC : P1 * w2 - P2 * w1 = σ * (Q1 * W2 - Q2 * W1))
    (hQ1 : kix = k0x + Q1) (hQ2 : kiy = k0y + Q2) (hD1 : lx - pix = D1 - P1)
    (hD2 : ly - piy = D2 - P2) :
    (k0x + ((D1 * w1 + D2 * w2) * W1 + σ * (D1 * w2 - D2 * w1) * W2) / (W1 ^ 2 + W2 ^ 2) - kix) ^ 2
      + (k0y + ((D1 * w1 + D2 * w2) * W2 - σ * (D1 * w2 - D2 * w1) * W1) / (W1 ^ 2 + W2 ^ 2)
        - kiy) ^ 2 = (lx - pix) ^ 2 + (ly - piy) ^ 2 := by
  rw [hD1, hD2, hQ1, hQ2]
  have e1 : (W1 ^ 2 + W2 ^ 2) * ((k0x + ((D1 * w1 + D2 * w2) * W1 + σ * (D1 * w2 - D2 * w1) * W2)
        / (W1 ^ 2 + W2 ^ 2) - (k0x + Q1)) ^ 2
      + (k0y + ((D1 * w1 + D2 * w2) * W2 - σ * (D1 * w2 - D2 * w1) * W1) / (W1 ^ 2 + W2 ^ 2)
        - (k0y + Q2)) ^ 2)
      = ((D1 * w1 + D2 * w2) - (Q1 * W1 + Q2 * W2)) ^ 2
        + (σ * (D1 * w2 - D2 * w1) - (Q1 * W2 - Q2 * W1)) ^ 2 := by
    field_simp
    ring
  have e2 : (W1 ^ 2 + W2 ^ 2) * ((D1 - P1) ^ 2 + (D2 - P2) ^ 2)
      = ((D1 * w1 + D2 * w2) - (P1 * w1 + P2 * w2)) ^ 2
        + ((D1 * w2 - D2 * w1) - (P1 * w2 - P2 * w1)) ^ 2 := by
    rw [← hs]
    ring
  have e3 : ((D1 * w2 - D2 * w1) - (P1 * w2 - P2 * w1)) ^ 2
      = (σ * (D1 * w2 - D2 * w1) - (Q1 * W2 - Q2 * W1)) ^ 2 := by
    rw [hC]
    linear_combination ((Q1 * W2 - Q2 * W1) ^ 2 - (D1 * w2 - D2 * w1) ^ 2) * hσ2
  apply mul_left_cancel₀ hne
  rw [e1, e2, e3, hA]


lemma transfer2 {ι : Type*} (px py kx ky : ι → ℝ) (i0 i1 : ι)
    (hd : ∀ i j, (px i - px j) ^ 2 + (py i - py j) ^ 2 = (kx i - kx j) ^ 2 + (ky i - ky j) ^ 2)
    (hne : (kx i1 - kx i0) ^ 2 + (ky i1 - ky i0) ^ 2 ≠ 0) :
    ∃ σ : ℝ, σ ^ 2 = 1 ∧ ∀ (lx ly : ℝ) (i : ι),
      (kx i0 + (((lx - px i0) * (px i1 - px i0) + (ly - py i0) * (py i1 - py i0)) * (kx i1 - kx i0)
        + σ * ((lx - px i0) * (py i1 - py i0) - (ly - py i0) * (px i1 - px i0)) * (ky i1 - ky i0))
        / ((kx i1 - kx i0) ^ 2 + (ky i1 - ky i0) ^ 2) - kx i) ^ 2
      + (ky i0 + (((lx - px i0) * (px i1 - px i0) + (ly - py i0) * (py i1 - py i0)) * (ky i1 - ky i0)
        - σ * ((lx - px i0) * (py i1 - py i0) - (ly - py i0) * (px i1 - px i0)) * (kx i1 - kx i0))
        / ((kx i1 - kx i0) ^ 2 + (ky i1 - ky i0) ^ 2) - ky i) ^ 2
      = (lx - px i) ^ 2 + (ly - py i) ^ 2 := by
  have hs : (px i1 - px i0) ^ 2 + (py i1 - py i0) ^ 2 = (kx i1 - kx i0) ^ 2 + (ky i1 - ky i0) ^ 2 :=
    hd i1 i0
  have hA : ∀ i, (px i - px i0) * (px i1 - px i0) + (py i - py i0) * (py i1 - py i0)
      = (kx i - kx i0) * (kx i1 - kx i0) + (ky i - ky i0) * (ky i1 - ky i0) := by
    intro i
    have h1 := hd i i0
    have h2 := hd i i1
    linear_combination (h1 + hs - h2) / 2
  have hC : ∀ i j, ((px i - px i0) * (py i1 - py i0) - (py i - py i0) * (px i1 - px i0)) *
        ((px j - px i0) * (py i1 - py i0) - (py j - py i0) * (px i1 - px i0))
      = ((kx i - kx i0) * (ky i1 - ky i0) - (ky i - ky i0) * (kx i1 - kx i0)) *
        ((kx j - kx i0) * (ky i1 - ky i0) - (ky j - ky i0) * (kx i1 - kx i0)) := by
    intro i j
    have hAi := hA i
    have hAj := hA j
    have h1 := hd i i0
    have h2 := hd j i0
    have h3 := hd i j
    linear_combination ((px i1 - px i0) ^ 2 + (py i1 - py i0) ^ 2) * (h1 + h2 - h3) / 2
      + (((kx i - kx i0) * (kx j - kx i0) + (ky i - ky i0) * (ky j - ky i0))) * hs
      - ((px i - px i0) * (px i1 - px i0) + (py i - py i0) * (py i1 - py i0)) * hAj
      - ((kx j - kx i0) * (kx i1 - kx i0) + (ky j - ky i0) * (ky i1 - ky i0)) * hAi
  obtain ⟨σ, hσ2, hσ⟩ := sign_lemma
    (fun i => (px i - px i0) * (py i1 - py i0) - (py i - py i0) * (px i1 - px i0))
    (fun i => (kx i - kx i0) * (ky i1 - ky i0) - (ky i - ky i0) * (kx i1 - kx i0)) hC
  exact ⟨σ, hσ2, fun lx ly i => alg_step (lx - px i0) (ly - py i0) (px i - px i0) (py i - py i0)
    (kx i - kx i0) (ky i - ky i0) (px i1 - px i0) (py i1 - py i0) (kx i1 - kx i0) (ky i1 - ky i0)
    σ (kx i0) (ky i0) (kx i) (ky i) (lx) (ly) (px i) (py i) hs hne hσ2 (hA i) (hσ i)
    (by ring) (by ring) (by ring) (by ring)⟩

lemma lattice_sep_int (da db : ℤ) (h : da ≠ 0 ∨ db ≠ 0) :
    64 ≤ 16 * (2 * da + db) ^ 2 + 49 * db ^ 2 := by
  have hc : db = 0 ∨ db = 1 ∨ db = -1 ∨ 2 ≤ db ∨ db ≤ -2 := by omega
  rcases hc with hc | hc | hc | hc | hc
  · subst hc
    have : da ≤ -1 ∨ 1 ≤ da := by omega
    rcases this with h2 | h2 <;> nlinarith
  · subst hc
    have : 2 * da + 1 ≤ -1 ∨ 1 ≤ 2 * da + 1 := by omega
    rcases this with h2 | h2 <;> nlinarith
  · subst hc
    have : 2 * da + -1 ≤ -1 ∨ 1 ≤ 2 * da + -1 := by omega
    rcases this with h2 | h2 <;> nlinarith
  · nlinarith [sq_nonneg (2 * da + db)]
  · nlinarith [sq_nonneg (2 * da + db)]


noncomputable def L (a b : ℤ) : ℝ² := !₂[2 * (a : ℝ) + b, 7 / 4 * (b : ℝ)]

def S : Set ℝ² := {x | ∃ a b : ℤ, dist x (L a b) < 1 / 2}

noncomputable def K (i : Fin 8) : ℝ² := !₂[(kxn i.val : ℝ) / 100, (kyn i.val : ℝ) / 100]

lemma dist_sq (x y : ℝ²) : dist x y ^ 2 = (x 0 - y 0) ^ 2 + (x 1 - y 1) ^ 2 := by
  rw [EuclideanSpace.dist_eq, Real.sq_sqrt (by positivity), Fin.sum_univ_two, Real.dist_eq,
    Real.dist_eq, sq_abs, sq_abs]

lemma L_sep (a b a' b' : ℤ) (h : (a, b) ≠ (a', b')) : 2 ≤ dist (L a b) (L a' b') := by
  have h1 : a - a' ≠ 0 ∨ b - b' ≠ 0 := by
    by_contra hc
    simp only [not_or, not_not] at hc
    apply h
    have e1 : a = a' := by omega
    have e2 : b = b' := by omega
    rw [e1, e2]
  have h2 := lattice_sep_int (a - a') (b - b') h1
  have h2' : (64 : ℝ) ≤ 16 * (2 * ((a : ℝ) - a') + ((b : ℝ) - b')) ^ 2 + 49 * ((b : ℝ) - b') ^ 2 := by
    exact_mod_cast h2
  have h3 : dist (L a b) (L a' b') ^ 2
      = (2 * (a : ℝ) + b - (2 * a' + b')) ^ 2 + (7 / 4 * (b : ℝ) - 7 / 4 * b') ^ 2 := by
    rw [dist_sq]
    simp [L]
  have h4 : (4 : ℝ) ≤ dist (L a b) (L a' b') ^ 2 := by
    rw [h3]
    nlinarith
  nlinarith [dist_nonneg (x := L a b) (y := L a' b')]

lemma S_avoid : Erdos214.UnitDistanceAvoiding S := by
  intro x hx y hy hxy
  obtain ⟨a, b, hab⟩ := hx
  obtain ⟨a', b', hab'⟩ := hy
  by_cases he : (a, b) = (a', b')
  · simp only [Prod.mk.injEq] at he
    obtain ⟨rfl, rfl⟩ := he
    have := dist_triangle_right x y (L a b)
    linarith
  · have h2 := L_sep a b a' b' he
    have t1 := dist_triangle (L a b) x (L a' b')
    have t2 := dist_triangle x y (L a' b')
    rw [dist_comm] at hab
    linarith

lemma K_inj_aux : ∀ i j : Fin 8, kxn i.val = kxn j.val → kyn i.val = kyn j.val → i = j := by
  decide

lemma K_inj : Function.Injective K := by
  intro i j h
  have h0 := congrArg (fun v : ℝ² => v 0) h
  have h1 := congrArg (fun v : ℝ² => v 1) h
  simp [K] at h0 h1
  exact K_inj_aux i j (by exact_mod_cast h0) (by exact_mod_cast h1)

lemma alg_fin (σ σ' lx ly px0 py0 px1 py1 kx0 ky0 kx1 ky1 A B κ1 κ2 u v : ℝ) (hk0 : kx0 = 0)
    (hk0' : ky0 = 0) (hW : (kx1 - kx0) ^ 2 + (ky1 - ky0) ^ 2 ≠ 0) (hσ2 : σ ^ 2 = 1)
    (hu : u = ((px1 - px0) * (kx1 - kx0) + σ * (py1 - py0) * (ky1 - ky0))
      / ((kx1 - kx0) ^ 2 + (ky1 - ky0) ^ 2))
    (hv : v = ((px1 - px0) * (ky1 - ky0) - σ * (py1 - py0) * (kx1 - kx0))
      / ((kx1 - kx0) ^ 2 + (ky1 - ky0) ^ 2))
    (huv : u ^ 2 + v ^ 2 = 1) (hσ' : σ' ^ 2 = 1) (hD1 : lx - px0 = 2 * A + B)
    (hD2 : ly - py0 = 7 / 4 * (σ' * σ) * B) :
    (kx0 + (((lx - px0) * (px1 - px0) + (ly - py0) * (py1 - py0)) * (kx1 - kx0)
        + σ * ((lx - px0) * (py1 - py0) - (ly - py0) * (px1 - px0)) * (ky1 - ky0))
        / ((kx1 - kx0) ^ 2 + (ky1 - ky0) ^ 2) - κ1) ^ 2
      + (ky0 + (((lx - px0) * (px1 - px0) + (ly - py0) * (py1 - py0)) * (ky1 - ky0)
        - σ * ((lx - px0) * (py1 - py0) - (ly - py0) * (px1 - px0)) * (kx1 - kx0))
        / ((kx1 - kx0) ^ 2 + (ky1 - ky0) ^ 2) - κ2) ^ 2
      = Dr σ' A B u v κ1 κ2 := by
  set D1 := lx - px0 with eD1
  set D2 := ly - py0 with eD2
  set w1 := px1 - px0 with ew1
  set w2 := py1 - py0 with ew2
  set W1 := kx1 - kx0 with eW1
  set W2 := ky1 - ky0 with eW2
  have ex : ((D1 * w1 + D2 * w2) * W1 + σ * (D1 * w2 - D2 * w1) * W2) / (W1 ^ 2 + W2 ^ 2)
      = D1 * u - σ * D2 * v := by
    rw [hu, hv]
    field_simp
    linear_combination (-(D2 * w2 * W1)) * hσ2
  have ey : ((D1 * w1 + D2 * w2) * W2 - σ * (D1 * w2 - D2 * w1) * W1) / (W1 ^ 2 + W2 ^ 2)
      = D1 * v + σ * D2 * u := by
    rw [hu, hv]
    field_simp
    linear_combination (-(D2 * w2 * W2)) * hσ2
  rw [ex, ey, hD1, hD2, hk0, hk0']
  unfold Dr
  linear_combination ((2 * A + B) ^ 2 + 49 / 16 * B ^ 2 * σ' ^ 2 * σ ^ 4) * huv
    + (49 / 16 * B ^ 2 * σ' ^ 2 * (σ ^ 2 + 1) - 7 / 2 * σ' * B * (κ2 * u - κ1 * v)) * hσ2
    + 49 / 16 * B ^ 2 * hσ'

lemma main (p : Fin 8 → ℝ²) (hpS : ∀ i, p i ∈ Sᶜ) (hc : p ≅ K) : False := by
  have hd : ∀ i j, (p i 0 - p j 0) ^ 2 + (p i 1 - p j 1) ^ 2
      = (K i 0 - K j 0) ^ 2 + (K i 1 - K j 1) ^ 2 := by
    intro i j
    rw [← dist_sq, ← dist_sq, (congruent_iff_dist_eq.mp hc) i j]
  have hK0 : K 0 0 = 0 ∧ K 0 1 = 0 := by simp [K, kxn, kyn]
  have hK1 : K 1 0 = 4 / 5 ∧ K 1 1 = 0 := by
    simp [K, kxn, kyn]
    norm_num
  have hne : (K 1 0 - K 0 0) ^ 2 + (K 1 1 - K 0 1) ^ 2 ≠ 0 := by
    rw [hK0.1, hK0.2, hK1.1, hK1.2]
    norm_num
  obtain ⟨σ, hσ2, hz⟩ := transfer2 (fun i => p i 0) (fun i => p i 1) (fun i => K i 0)
    (fun i => K i 1) 0 1 hd hne
  simp only at hz
  have hs : (p 1 0 - p 0 0) ^ 2 + (p 1 1 - p 0 1) ^ 2
      = (K 1 0 - K 0 0) ^ 2 + (K 1 1 - K 0 1) ^ 2 := hd 1 0
  obtain ⟨u, hu⟩ : ∃ u : ℝ, u = ((p 1 0 - p 0 0) * (K 1 0 - K 0 0)
      + σ * (p 1 1 - p 0 1) * (K 1 1 - K 0 1)) / ((K 1 0 - K 0 0) ^ 2 + (K 1 1 - K 0 1) ^ 2) :=
    ⟨_, rfl⟩
  obtain ⟨v, hv⟩ : ∃ v : ℝ, v = ((p 1 0 - p 0 0) * (K 1 1 - K 0 1)
      - σ * (p 1 1 - p 0 1) * (K 1 0 - K 0 0)) / ((K 1 0 - K 0 0) ^ 2 + (K 1 1 - K 0 1) ^ 2) :=
    ⟨_, rfl⟩
  have huv' : ((p 1 0 - p 0 0) * (K 1 0 - K 0 0) + σ * (p 1 1 - p 0 1) * (K 1 1 - K 0 1)) ^ 2
      + ((p 1 0 - p 0 0) * (K 1 1 - K 0 1) - σ * (p 1 1 - p 0 1) * (K 1 0 - K 0 0)) ^ 2
      = ((K 1 0 - K 0 0) ^ 2 + (K 1 1 - K 0 1) ^ 2) ^ 2 := by
    linear_combination ((K 1 0 - K 0 0) ^ 2 + (K 1 1 - K 0 1) ^ 2) * hs
      + ((K 1 0 - K 0 0) ^ 2 + (K 1 1 - K 0 1) ^ 2) * (p 1 1 - p 0 1) ^ 2 * hσ2
  have huv : u ^ 2 + v ^ 2 = 1 := by
    rw [hu, hv, div_pow, div_pow, ← add_div, huv', div_self (pow_ne_zero 2 hne)]
  have key : ∀ (c : ℕ) (LA LB : ℤ) (A' B' σ' : ℝ), σ' ^ 2 = 1 →
      2 * (LA : ℝ) + LB - p 0 0 = 2 * A' + B' → 7 / 4 * (LB : ℝ) - p 0 1 = 7 / 4 * (σ' * σ) * B' →
      Dr σ' A' B' u v ((kxn (c % 8) : ℝ) / 100) ((kyn (c % 8) : ℝ) / 100) < 1 / 4 → False := by
    intro c LA LB A' B' σ' hσ' hD1 hD2 hlt
    let i : Fin 8 := ⟨c % 8, Nat.mod_lt _ (by norm_num)⟩
    have hKi : K i 0 = (kxn (c % 8) : ℝ) / 100 ∧ K i 1 = (kyn (c % 8) : ℝ) / 100 := by
      simp [K, i]
    have h := hz (2 * (LA : ℝ) + LB) (7 / 4 * (LB : ℝ)) i
    rw [alg_fin σ σ' (2 * (LA : ℝ) + LB) (7 / 4 * (LB : ℝ)) (p 0 0) (p 0 1) (p 1 0) (p 1 1)
      (K 0 0) (K 0 1) (K 1 0) (K 1 1) A' B' (K i 0) (K i 1) u v hK0.1 hK0.2 hne hσ2 hu hv huv hσ'
      hD1 hD2, hKi.1, hKi.2] at h
    apply hpS i
    refine ⟨LA, LB, ?_⟩
    have e0 : (L LA LB) 0 = 2 * (LA : ℝ) + LB := by simp [L]
    have e1 : (L LA LB) 1 = 7 / 4 * (LB : ℝ) := by simp [L]
    have hdl : dist (p i) (L LA LB) ^ 2 < 1 / 4 := by
      rw [dist_sq, e0, e1]
      have q0 : (p i 0 - (2 * (LA : ℝ) + LB)) ^ 2 = (2 * (LA : ℝ) + LB - p i 0) ^ 2 := by ring
      have q1 : (p i 1 - 7 / 4 * (LB : ℝ)) ^ 2 = (7 / 4 * (LB : ℝ) - p i 1) ^ 2 := by ring
      rw [q0, q1, ← h]
      exact hlt
    have h4 : (1 / 2 : ℝ) ^ 2 = 1 / 4 := by norm_num
    exact lt_of_pow_lt_pow_left₀ 2 (by norm_num) (by rw [h4]; exact hdl)
  have hσc : σ = 1 ∨ σ = -1 := by
    have : (σ - 1) * (σ + 1) = 0 := by linear_combination hσ2
    rcases mul_eq_zero.mp this with h | h
    · left; linarith
    · right; linarith
  obtain ⟨sg, hsg, hsgσ⟩ : ∃ sg : ℤ, (sg = 1 ∨ sg = -1) ∧ (sg : ℝ) = σ := by
    rcases hσc with h | h
    · exact ⟨1, Or.inl rfl, by rw [h]; norm_num⟩
    · exact ⟨-1, Or.inr rfl, by rw [h]; norm_num⟩
  have hb1 : ((⌊4 * p 0 1 / 7⌋ : ℤ) : ℝ) ≤ 4 * p 0 1 / 7 := Int.floor_le _
  have hb2 : 4 * p 0 1 / 7 < ((⌊4 * p 0 1 / 7⌋ : ℤ) : ℝ) + 1 := Int.lt_floor_add_one _
  have ha1 : ((⌊(p 0 0 - 4 * p 0 1 / 7) / 2⌋ : ℤ) : ℝ) ≤ (p 0 0 - 4 * p 0 1 / 7) / 2 :=
    Int.floor_le _
  have ha2 : (p 0 0 - 4 * p 0 1 / 7) / 2 < ((⌊(p 0 0 - 4 * p 0 1 / 7) / 2⌋ : ℤ) : ℝ) + 1 :=
    Int.lt_floor_add_one _
  generalize ⌊4 * p 0 1 / 7⌋ = b0 at hb1 hb2
  generalize ⌊(p 0 0 - 4 * p 0 1 / 7) / 2⌋ = a0 at ha1 ha2
  have hX : p 0 0 = 2 * (a0 : ℝ) + b0 + 2 * ((p 0 0 - 4 * p 0 1 / 7) / 2 - a0)
      + (4 * p 0 1 / 7 - b0) := by ring
  have hY : p 0 1 = 7 / 4 * ((b0 : ℝ) + (4 * p 0 1 / 7 - b0)) := by ring
  generalize hα : (p 0 0 - 4 * p 0 1 / 7) / 2 - a0 = α at hX
  generalize hβ : 4 * p 0 1 / 7 - (b0 : ℝ) = β at hX hY
  have hα0 : 0 ≤ α := by rw [← hα]; linarith
  have hα1 : α < 1 := by rw [← hα]; linarith
  have hβ0 : 0 ≤ β := by rw [← hβ]; linarith
  have hβ1 : β < 1 := by rw [← hβ]; linarith
  rcases le_total (α + β) 1 with hup | hdn
  · obtain ⟨c, hc⟩ := geo sg hsg u v α β huv hα0 hβ0 hup
    refine key c (a0 + amn (c / 8)) (b0 + bmn (c / 8)) (amn (c / 8) - α) (bmn (c / 8) - β) sg
      (by rcases hsg with h | h <;> rw [h] <;> norm_num) ?_ ?_ hc
    · rw [hX]; push_cast; ring
    · rw [hY, ← hsgσ]
      have : ((sg : ℝ)) * sg = 1 := by rcases hsg with h | h <;> rw [h] <;> norm_num
      push_cast
      linear_combination (-(7 / 4) * ((bmn (c / 8) : ℝ) - β)) * this
  · obtain ⟨c, hc⟩ := geo (-sg) (by rcases hsg with h | h <;> rw [h] <;> norm_num) u v (α + β - 1)
      (1 - β) huv (by linarith) (by linarith) (by linarith)
    refine key c (a0 + amn (c / 8) + bmn (c / 8)) (b0 + 1 - bmn (c / 8)) (amn (c / 8) - (α + β - 1))
      (bmn (c / 8) - (1 - β)) ((-sg : ℤ) : ℝ)
      (by rcases hsg with h | h <;> rw [h] <;> norm_num) ?_ ?_ hc
    · rw [hX]; push_cast; ring
    · rw [hY, ← hsgσ]
      have : ((sg : ℝ)) * sg = 1 := by rcases hsg with h | h <;> rw [h] <;> norm_num
      push_cast
      linear_combination (7 / 4 * ((bmn (c / 8) : ℝ) - (1 - β))) * this

end OMA214C

theorem OMA.solution : type_of% @Erdos214.erdos_214.variants.csizmadia_toth := by
  intro hR
  obtain ⟨p, hpS, hc⟩ := hR OMA214C.S OMA214C.S_avoid OMA214C.K OMA214C.K_inj
  exact OMA214C.main p hpS hc
