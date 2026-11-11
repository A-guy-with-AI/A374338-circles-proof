import Mathlib

/-! # Cercles de Shannon et croissance de Markey

Les coordonnées (u,y) représentent un réseau triangulaire pour chaque parité
de u+y. On démontre la forme à chaque tour et les formules de cardinalité.
Le lien avec les intersections de cercles unité est démontré dans ℂ.

Les arcs sont modélisés par les incidences centre–sommet. Le nombre de
régions est défini par E - V + 1. L'identification des arcs topologiques
avec ces incidences et le théorème d'Euler planaire relèvent de la preuve
sur papier.
-/

namespace Cercles

abbrev Site := ℤ × ℤ

def shift (p : Site) (dx dy : ℤ) : Site := (p.1 + dx, p.2 + dy)

def neighbor (p q : Site) : Prop :=
  q = shift p 2 0 ∨ q = shift p (-2) 0 ∨
  q = shift p 1 1 ∨ q = shift p (-1) 1 ∨
  q = shift p 1 (-1) ∨ q = shift p (-1) (-1)

def grow (S : Set Site) : Set Site :=
  {p | p ∈ S ∨ ∃ q r, q ≠ r ∧ neighbor p q ∧ neighbor p r ∧ q ∈ S ∧ r ∈ S}

def hex (a b parity : ℤ) : Set Site :=
  {p | (p.1 + p.2) % 2 = parity ∧ |p.1| ≤ a ∧ |p.1| + 3 * |p.2| ≤ b}

private theorem mem_hex {a b s x y : ℤ} :
    (x, y) ∈ hex a b s ↔ (x + y) % 2 = s ∧
      -a ≤ x ∧ x ≤ a ∧
      x + 3*y ≤ b ∧ x - 3*y ≤ b ∧ -x + 3*y ≤ b ∧ -x - 3*y ≤ b := by
  change (_ ∧ _ ∧ _) ↔ _
  rw [abs_le]
  by_cases hx : x < 0 <;> by_cases hy : y < 0
  all_goals
    have hx' : |x| = (if x < 0 then -x else x) := by split <;> simp_all [abs_of_neg, abs_of_nonneg]
    have hy' : |y| = (if y < 0 then -y else y) := by split <;> simp_all [abs_of_neg, abs_of_nonneg]
    rw [hx', hy']
    simp only [hx, hy, ite_true, ite_false]
    omega

private theorem grow_intro {S : Set Site} {p : Site} {dx dy ex ey : ℤ}
    (hq : neighbor p (shift p dx dy)) (hr : neighbor p (shift p ex ey))
    (h : shift p dx dy ≠ shift p ex ey)
    (hs : shift p dx dy ∈ S) (ht : shift p ex ey ∈ S) : p ∈ grow S :=
  Or.inr ⟨_, _, h, hq, hr, hs, ht⟩

private theorem hex_upper {a b s x y : ℤ}
    (hb : b % 2 = s) (h : (x, y) ∈ grow (hex a b s)) :
    (x, y) ∈ hex (a+1) (b+2) s := by
  change _ ∨ _ at h
  rw [mem_hex]
  rcases h with h | ⟨q, r, hne, hq, hr, hqS, hrS⟩
  · rw [mem_hex] at h
    omega
  · rcases hq with rfl | rfl | rfl | rfl | rfl | rfl <;>
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    all_goals try exact (hne rfl).elim
    all_goals simp only [shift, mem_hex] at hne hqS hrS
    all_goals omega

private def reflect (i j : Bool) (p : Site) : Site :=
  (if i then -p.1 else p.1, if j then -p.2 else p.2)

private theorem reflect_twice (i j : Bool) (p : Site) :
    reflect i j (reflect i j p) = p := by
  rcases p with ⟨x,y⟩
  cases i <;> cases j <;> simp [reflect]

private theorem reflect_hex (i j : Bool) (p : Site) (a b s : ℤ) :
    reflect i j p ∈ hex a b s ↔ p ∈ hex a b s := by
  rcases p with ⟨x,y⟩
  cases i <;> cases j <;> simp [reflect, mem_hex] <;> omega

private theorem reflect_neighbor (i j : Bool) {p q : Site} (h : neighbor p q) :
    neighbor (reflect i j p) (reflect i j q) := by
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl <;>
    cases i <;> cases j <;> simp [neighbor, reflect, shift] <;> omega

private theorem reflect_grow (i j : Bool) {p : Site} {a b s : ℤ}
    (h : p ∈ grow (hex a b s)) : reflect i j p ∈ grow (hex a b s) := by
  rcases h with h | ⟨q,r,hne,hq,hr,hqs,hrs⟩
  · exact Or.inl ((reflect_hex ..).2 h)
  · refine Or.inr ⟨_, _, ?_, reflect_neighbor i j hq, reflect_neighbor i j hr,
      (reflect_hex ..).2 hqs, (reflect_hex ..).2 hrs⟩
    intro he
    apply hne
    simpa only [reflect_twice] using congrArg (reflect i j) he

private theorem hex_lower_quadrant {a b s x y : ℤ}
    (ha : 2 ≤ a) (hab : a + 2 ≤ b) (hb : b % 2 = s)
    (hx : 0 ≤ x) (hy : 0 ≤ y) (hp : (x,y) ∈ hex (a+1) (b+2) s) :
    (x,y) ∈ grow (hex a b s) := by
  rw [mem_hex] at hp
  by_cases hOld : (x,y) ∈ hex a b s
  · exact Or.inl hOld
  rw [mem_hex] at hOld
  by_cases hside : x = a + 1
  · by_cases hbottom : y = 0
    · apply grow_intro (dx := -1) (dy := 1) (ex := -1) (ey := -1)
      all_goals first | (simp [neighbor, shift, mem_hex]; done) | (simp [shift, mem_hex]; omega)
    · apply grow_intro (dx := -2) (dy := 0) (ex := -1) (ey := -1)
      all_goals first | (simp [neighbor, shift, mem_hex]; done) | (simp [shift, mem_hex]; omega)
  · by_cases hedge : x = a
    · apply grow_intro (dx := -2) (dy := 0) (ex := -1) (ey := -1)
      all_goals first | (simp [neighbor, shift, mem_hex]; done) | (simp [shift, mem_hex]; omega)
    · apply grow_intro (dx := 1) (dy := -1) (ex := -1) (ey := -1)
      all_goals first | (simp [neighbor, shift, mem_hex]; done) | (simp [shift, mem_hex]; omega)

theorem grow_hex {a b s : ℤ} (ha : 2 ≤ a) (hab : a+2 ≤ b) (hb : b % 2 = s) :
    grow (hex a b s) = hex (a+1) (b+2) s := by
  ext ⟨x,y⟩
  constructor
  · exact hex_upper hb
  · intro hp
    let i := decide (x < 0)
    let j := decide (y < 0)
    have hp' := (reflect_hex i j (x,y) _ _ _).2 hp
    have hx : 0 ≤ (reflect i j (x,y)).1 := by simp [reflect, i]; split <;> omega
    have hy : 0 ≤ (reflect i j (x,y)).2 := by simp [reflect, j]; split <;> omega
    have hg := hex_lower_quadrant ha hab hb hx hy hp'
    change reflect i j (x,y) ∈ grow (hex a b s) at hg
    simpa only [reflect_twice] using reflect_grow i j hg

open Finset

def nearFin (p : Site) : Finset Site :=
  {shift p 2 0, shift p (-2) 0, shift p 1 1, shift p (-1) 1,
    shift p 1 (-1), shift p (-1) (-1)}

@[simp] theorem mem_nearFin {p q : Site} : q ∈ nearFin p ↔ neighbor p q := by
  simp [nearFin, neighbor]

theorem neighbor_symm {p q : Site} (h : neighbor p q) : neighbor q p := by
  rcases p with ⟨x,y⟩
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp [neighbor, shift, Prod.mk.injEq]

def growFin (S : Finset Site) : Finset Site :=
  S ∪ (S.biUnion nearFin).filter (fun p => 1 < (S ∩ nearFin p).card)

@[simp] theorem coe_growFin (S : Finset Site) :
    (growFin S : Set Site) = grow (S : Set Site) := by
  ext p
  simp only [growFin, coe_union, coe_filter, Set.mem_union, Set.mem_ofPred_eq, mem_coe,
    mem_biUnion, mem_nearFin, one_lt_card, mem_inter]
  change (_ ∨ _) ↔ (_ ∨ ∃ q r, _)
  constructor
  · rintro (hp | ⟨_, q, ⟨hq, hqp⟩, r, ⟨hr, hrp⟩, hne⟩)
    · exact Or.inl hp
    · exact Or.inr ⟨q,r,hne,hqp,hrp,hq,hr⟩
  · rintro (hp | ⟨q,r,hne,hqp,hrp,hq,hr⟩)
    · exact Or.inl hp
    · exact Or.inr ⟨⟨q,hq,neighbor_symm hqp⟩,q,⟨hq,hqp⟩,r,⟨hr,hrp⟩,hne⟩

def hexFin (a b s : ℤ) : Finset Site :=
  ((Icc (-a) a) ×ˢ (Icc (-b) b)).filter
    (fun p => (p.1+p.2)%2 = s ∧ |p.1| + 3*|p.2| ≤ b)

@[simp] theorem coe_hexFin (a b s : ℤ) : (hexFin a b s : Set Site) = hex a b s := by
  ext ⟨x,y⟩
  change (x,y) ∈ ((Icc (-a) a) ×ˢ (Icc (-b) b)).filter _ ↔ _
  rw [Finset.mem_filter, Finset.mem_product, Finset.mem_Icc, Finset.mem_Icc, mem_hex]
  by_cases hx : x < 0 <;> by_cases hy : y < 0
  all_goals
    have hxa : |x| = (if x < 0 then -x else x) := by split <;> simp_all [abs_of_neg, abs_of_nonneg]
    have hya : |y| = (if y < 0 then -y else y) := by split <;> simp_all [abs_of_neg, abs_of_nonneg]
    rw [hxa,hya]
    simp only [hx, hy, ite_true, ite_false]
    omega

def seedShannon : Finset Site := {(-1,0),(1,0)}

def seedMarkey : Finset Site := {(-4,0),(-2,0),(0,0),(2,0),(4,0)}

def shannonHex (n : ℕ) : Finset Site := hexFin n (2*(n : ℤ)+1) 1

def markeyHex (n : ℕ) : Finset Site := hexFin ((n : ℤ)+3) (2*(n : ℤ)+4) 0

def iterate (S : Finset Site) (n : ℕ) : Finset Site := (growFin^[n]) S

private theorem iterate_succ (S : Finset Site) (n : ℕ) :
    iterate S (n+1) = growFin (iterate S n) := Function.iterate_succ_apply' ..

theorem shannon_shape (n : ℕ) (hn : 1 ≤ n) : iterate seedShannon n = shannonHex n := by
  induction n with
  | zero => omega
  | succ n ih =>
    by_cases h0 : n = 0
    · subst n
      decide
    by_cases h1 : n = 1
    · subst n
      decide
    rw [iterate_succ, ih (by omega)]
    apply coe_injective
    simp only [shannonHex, coe_growFin, coe_hexFin, Nat.cast_succ]
    convert grow_hex (a := (n : ℤ)) (b := 2*(n : ℤ)+1) (s := 1)
      (by omega) (by omega) (by omega) using 2; omega

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1000000 in
theorem markey_shape (n : ℕ) (hn : 2 ≤ n) : iterate seedMarkey n = markeyHex n := by
  induction n with
  | zero => omega
  | succ n ih =>
    by_cases h1 : n = 1
    · subst n
      decide
    have hn' : 2 ≤ n := by omega
    rw [iterate_succ, ih hn']
    apply coe_injective
    simp only [markeyHex, coe_growFin, coe_hexFin, Nat.cast_succ]
    convert grow_hex (a := (n : ℤ)+3) (b := 2*(n : ℤ)+4) (s := 0)
      (by omega) (by omega) (by omega) using 2 <;> omega

private theorem mem_hexFin {a b s x y : ℤ} :
    (x,y) ∈ hexFin a b s ↔ (x + y) % 2 = s ∧
      -a ≤ x ∧ x ≤ a ∧
      x + 3*y ≤ b ∧ x - 3*y ≤ b ∧ -x + 3*y ≤ b ∧ -x - 3*y ≤ b := by
  rw [← mem_coe, coe_hexFin, mem_hex]

/-- Les deux côtés verticaux, paramétrés par l’entier k dans y = 2k + r. -/
private def side (a k r : ℤ) : Finset Site :=
  (univ ×ˢ (Icc ((-k-r+1)/2) ((k-r)/2))).image
    (fun (p : Bool × ℤ) => (if p.1 then a else -a, 2*p.2+r))

private theorem mem_side {a k r x y : ℤ} (hr : 0 ≤ r ∧ r < 2) :
    (x,y) ∈ side a k r ↔ (x = a ∨ x = -a) ∧ -k ≤ y ∧ y ≤ k ∧ y % 2 = r := by
  simp only [side, mem_image, Prod.exists, mem_product, mem_univ, true_and, mem_Icc,
    Prod.mk.injEq, Bool.exists_bool, Bool.false_eq_true, ite_false, ite_true]
  constructor
  · rintro (⟨i, hi, hx, hy⟩ | ⟨i, hi, hx, hy⟩) <;> omega
  · rintro ⟨hx | hx, hy⟩
    · exact Or.inr ⟨(y-r)/2, by omega, by omega, by omega⟩
    · exact Or.inl ⟨(y-r)/2, by omega, by omega, by omega⟩

/-- Les deux calottes obliques pour un signe donné de la coordonnée horizontale. -/
private def cap (b lo hi : ℤ) (negative : Bool) : Finset Site :=
  (univ ×ˢ (Icc lo hi)).image (fun (p : Bool × ℤ) =>
    (if negative then -(b-3*p.2) else b-3*p.2, if p.1 then p.2 else -p.2))

private theorem mem_cap {b lo hi x y : ℤ} {negative : Bool} :
    (x,y) ∈ cap b lo hi negative ↔
      ∃ t, lo ≤ t ∧ t ≤ hi ∧ (y = t ∨ y = -t) ∧
        x = if negative then -(b-3*t) else b-3*t := by
  simp only [cap, mem_image, Prod.exists, mem_product, mem_univ, true_and, mem_Icc,
    Prod.mk.injEq, Bool.exists_bool, Bool.false_eq_true, ite_false, ite_true]
  constructor
  · rintro (⟨t, ⟨hl,hu⟩, hx, hy⟩ | ⟨t, ⟨hl,hu⟩, hx, hy⟩)
    · exact ⟨t,hl,hu,Or.inr hy.symm,hx.symm⟩
    · exact ⟨t,hl,hu,Or.inl hy.symm,hx.symm⟩
  · rintro ⟨t,hl,hu,hy | hy,hx⟩
    · exact Or.inr ⟨t,⟨hl,hu⟩,hx.symm,hy.symm⟩
    · exact Or.inl ⟨t,⟨hl,hu⟩,hx.symm,hy.symm⟩

private theorem card_side {a k r : ℤ} (ha : 0 < a) :
    ((side a k r).card : ℤ) = 2 * ((Icc ((-k-r+1)/2) ((k-r)/2)).card : ℤ) := by
  rw [side, card_image_of_injOn, card_product]
  · simp
  · rintro ⟨i,x⟩ _ ⟨j,y⟩ _ he
    cases i <;> cases j <;> simp at he ⊢ <;> omega

private theorem card_cap {b lo hi : ℤ} (hl : 0 < lo) (negative : Bool) :
    ((cap b lo hi negative).card : ℤ) = 2 * ((Icc lo hi).card : ℤ) := by
  rw [cap, card_image_of_injOn, card_product]
  · simp
  · rintro ⟨i,x⟩ hx ⟨j,y⟩ hy he
    simp at hx hy
    cases negative <;> cases i <;> cases j <;> simp at he ⊢ <;> omega

private def rim (a b k lo r : ℤ) : Finset Site :=
  side a k r ∪ (cap b lo (b/3) false ∪ cap b lo ((b-1)/3) true)

private theorem layer_eq_rim {a b s : ℤ} (ha : 0 ≤ a) (hab : a + 2 ≤ b)
    (hb : b%2 = s) :
    hexFin (a+1) (b+2) s \ hexFin a b s =
      rim (a+1) (b+2) ((b+1-a)/3) ((b+4-a)/3) ((s-a-1)%2) := by
  ext ⟨x,y⟩
  simp only [mem_sdiff, mem_hexFin, rim, mem_union,
    mem_side (a := a+1) (k := (b+1-a)/3) (r := (s-a-1)%2) (by omega),
    mem_cap, Bool.false_eq_true, ite_true, ite_false]
  constructor
  · rintro ⟨hp, hn⟩
    by_cases hs : x = a+1 ∨ x = -(a+1)
    · exact Or.inl ⟨hs, by omega, by omega, by omega⟩
    right
    have hx : -a ≤ x ∧ x ≤ a := by omega
    by_cases hxp : 0 ≤ x
    · left
      by_cases hyp : 0 ≤ y
      · exact ⟨y, by omega, by omega, Or.inl rfl, by omega⟩
      · exact ⟨-y, by omega, by omega, Or.inr (by omega), by omega⟩
    · right
      by_cases hyp : 0 ≤ y
      · exact ⟨y, by omega, by omega, Or.inl rfl, by omega⟩
      · exact ⟨-y, by omega, by omega, Or.inr (by omega), by omega⟩
  · rintro (hs | ⟨t, hl, hu, hy, hx⟩ | ⟨t, hl, hu, hy, hx⟩) <;> omega

private theorem card_rimParts {a b k lo hiPos hiNeg r : ℤ}
    (ha : 0 < a) (hl : 0 < lo) (hab : b - 3*lo < a)
    (hPos : 3*hiPos ≤ b) (hNeg : 3*hiNeg < b) :
    ((side a k r ∪ (cap b lo hiPos false ∪ cap b lo hiNeg true)).card : ℤ) =
      2 * ((Icc ((-k-r+1)/2) ((k-r)/2)).card : ℤ) +
      2 * ((Icc lo hiPos).card : ℤ) + 2 * ((Icc lo hiNeg).card : ℤ) := by
  have hCaps : Disjoint (cap b lo hiPos false) (cap b lo hiNeg true) := by
    rw [disjoint_left]
    rintro ⟨x,y⟩ hp hn
    rw [mem_cap] at hp hn
    obtain ⟨t, htl, htu, _, hx⟩ := hp
    obtain ⟨v, hvl, hvu, _, hx'⟩ := hn
    simp at hx hx'
    omega
  have hSide : Disjoint (side a k r) (cap b lo hiPos false ∪ cap b lo hiNeg true) := by
    rw [disjoint_left]
    rintro ⟨x,y⟩ hs hp
    have hx : x = a ∨ x = -a := by
      simp only [side, mem_image] at hs
      obtain ⟨⟨i,t⟩, _, ht⟩ := hs
      cases i <;> simp_all
    rw [mem_union, mem_cap, mem_cap] at hp
    rcases hp with ⟨t, htl, htu, _, hxt⟩ | ⟨t, htl, htu, _, hxt⟩ <;>
      simp at hxt <;> omega
  rw [card_union_of_disjoint hSide, card_union_of_disjoint hCaps]
  push_cast
  rw [card_side ha, card_cap hl, card_cap hl]
  ring

private theorem hexFin_mono {a b s : ℤ} : hexFin a b s ⊆ hexFin (a+1) (b+2) s := by
  rintro ⟨x,y⟩ hp
  rw [mem_hexFin] at hp ⊢
  omega

private theorem layer_card {a b s : ℤ} (ha : 0 ≤ a) (hab : a+2 ≤ b) (hb : b%2 = s) :
    ((hexFin (a+1) (b+2) s).card : ℤ) - (hexFin a b s).card =
      2 * (((b+1-a)/3-(s-a-1)%2)/2 - (-( (b+1-a)/3 )-(s-a-1)%2+1)/2 + 1)
      + 2 * ((b+2)/3 - (b+4-a)/3 + 1) + 2 * ((b+1)/3 - (b+4-a)/3 + 1) := by
  rw [← Nat.cast_sub (card_mono hexFin_mono), ← card_sdiff_of_subset hexFin_mono,
    layer_eq_rim ha hab hb, rim, card_rimParts (by omega) (by omega) (by omega) (by omega) (by omega)]
  simp only [Int.card_Icc]
  omega


def correction (n : ℤ) : ℤ := if n % 3 = 0 then 0 else if n % 3 = 1 then 4 else 2

private def newVertices (n : ℤ) : ℤ := 2*n + (if n%3 = 0 then 4 else 2)

private theorem shannon_layer (n : ℕ) (hn : 1 ≤ n) :
    ((shannonHex (n+1)).card : ℤ) - (shannonHex n).card = newVertices n := by
  unfold shannonHex newVertices
  push_cast
  have h := layer_card (a := (n : ℤ)) (b := 2*(n : ℤ)+1) (s := 1)
    (by omega) (by omega) (by omega)
  rw [show 2*((n : ℤ)+1)+1 = 2*(n : ℤ)+1+2 by ring]
  rw [h]
  have hlo : 0 ≤ (n : ℤ)%6 := by omega
  have hhi : (n : ℤ)%6 ≤ 5 := by omega
  interval_cases hmod : (n : ℤ)%6 <;> omega

private theorem markey_layer (n : ℕ) (hn : 2 ≤ n) :
    ((markeyHex (n+1)).card : ℤ) - (markeyHex n).card = newVertices n + 4 := by
  unfold markeyHex newVertices
  push_cast
  have h := layer_card (a := (n : ℤ)+3) (b := 2*(n : ℤ)+4) (s := 0)
    (by omega) (by omega) (by omega)
  rw [show (n : ℤ)+1+3 = (n : ℤ)+3+1 by ring,
    show 2*((n : ℤ)+1)+4 = 2*(n : ℤ)+4+2 by ring, h]
  have hlo : 0 ≤ (n : ℤ)%6 := by omega
  have hhi : (n : ℤ)%6 ≤ 5 := by omega
  interval_cases hmod : (n : ℤ)%6 <;> omega

private theorem correction_step (n : ℤ) :
    3 * newVertices n = 6*n + 8 + correction (n+1) - correction n := by
  unfold correction newVertices
  omega

theorem shannon_hex_card (n : ℕ) (hn : 1 ≤ n) :
    3 * ((shannonHex n).card : ℤ) = 3*(n : ℤ)^2 + 5*(n : ℤ) + correction n := by
  induction n with
  | zero => omega
  | succ n ih =>
    by_cases h0 : n = 0
    · subst n
      decide
    have h := shannon_layer n (by omega)
    have hc := correction_step n
    have hi := ih (by omega)
    push_cast
    linear_combination 3*h + hi + hc

theorem markey_hex_difference (n : ℕ) (hn : 2 ≤ n) :
    ((markeyHex n).card : ℤ) = (shannonHex n).card + 4*(n : ℤ) + 7 := by
  induction n with
  | zero => omega
  | succ n ih =>
    by_cases h1 : n = 1
    · subst n
      decide
    have h := markey_layer n (by omega)
    have hs := shannon_layer n (by omega)
    have hi := ih (by omega)
    push_cast
    omega

theorem shannon_vertices (n : ℕ) (hn : 1 ≤ n) :
    ((iterate seedShannon n).card : ℤ) = (3*(n : ℤ)^2 + 5*(n : ℤ) + correction n)/3 := by
  rw [shannon_shape n hn, ← shannon_hex_card n hn]
  omega

theorem markey_vertices (n : ℕ) (hn : 2 ≤ n) :
    ((iterate seedMarkey n).card : ℤ) =
      (3*(n : ℤ)^2 + 17*(n : ℤ) + 21 + correction n)/3 := by
  rw [markey_shape n hn, markey_hex_difference n hn]
  have h := shannon_hex_card n (by omega)
  omega

/-! Les arcs se comptent par les incidences (centre, sommet). -/

def arcCount (centers vertices : Finset Site) : ℕ :=
  ∑ c ∈ centers, ((nearFin c).filter (· ∈ vertices)).card

def edgeCount (n : ℕ) : ℕ := arcCount (iterate seedShannon (n-1)) (iterate seedShannon n)

def regionCount (n : ℕ) : ℤ := (edgeCount n : ℤ) - (iterate seedShannon n).card + 1

private theorem nearFin_card (p : Site) : (nearFin p).card = 6 := by
  rcases p with ⟨x,y⟩
  have h (dx dy ex ey : ℤ) :
      shift (x,y) dx dy = shift (x,y) ex ey ↔ dx = ex ∧ dy = ey := by
    simp [shift]
  simp [nearFin, h, card_insert_of_notMem]

private def missed (C V : Finset Site) : Finset (Σ _ : Site, Site) :=
  (C.sigma nearFin).filter (fun p => p.2 ∉ V)

private theorem mem_missed {C V : Finset Site} {c p : Site} :
    (⟨c,p⟩ : Σ _ : Site, Site) ∈ missed C V ↔ c ∈ C ∧ neighbor p c ∧ p ∉ V := by
  simp only [missed, mem_filter, mem_sigma, mem_nearFin, and_assoc]
  exact and_congr_right fun _ => and_congr_left fun _ => ⟨neighbor_symm, neighbor_symm⟩

private theorem arc_add_missed (C V : Finset Site) :
    arcCount C V + (missed C V).card = 6 * C.card := by
  rw [arcCount, missed, filter_sigma C nearFin (fun p => p.2 ∉ V), card_sigma, ← sum_add_distrib]
  simp only [card_filter_add_card_filter_not, nearFin_card, sum_const, smul_eq_mul]
  omega

private def missedShape (n : ℤ) (p : Site) : Prop :=
  (p.1+p.2)%2 = 1 ∧
    ((|p.1| = n+2 ∧ 3*|p.2| ≤ n+1) ∨
      (1 ≤ |p.1| ∧ |p.1| ≤ n+1 ∧ |p.1|+3*|p.2| = 2*n+5))

private def hasMissed (n : ℤ) (p : Site) : Prop :=
  p ∉ hex (n+1) (2*n+3) 1 ∧ ∃ q ∈ hex n (2*n+1) 1, neighbor p q

private theorem missed_quadrant {n x y : ℤ} (hn : 1 ≤ n) (hx : 0 ≤ x) (hy : 0 ≤ y) :
    hasMissed n (x,y) ↔ missedShape n (x,y) := by
  simp only [hasMissed, mem_hex, missedShape, abs_of_nonneg hx,
    abs_of_nonneg hy]
  constructor
  · rintro ⟨hp, q, hq, hN⟩
    rcases hN with rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp only [shift, mem_hex] at hq <;> omega
  · rintro ⟨hP, ⟨hSide, hY⟩ | ⟨hX, hX', hCap⟩⟩
    · refine ⟨by omega, shift (x,y) (-2) 0, ?_, Or.inr (Or.inl rfl)⟩
      simp only [shift, mem_hex]
      omega
    · refine ⟨by omega, shift (x,y) (-1) (-1), ?_, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl))))⟩
      simp only [shift, mem_hex]
      omega

private theorem reflect_missed (n : ℤ) (i j : Bool) (p : Site)
    (h : hasMissed n p) : hasMissed n (reflect i j p) := by
  obtain ⟨hp,q,hq,hN⟩ := h
  exact ⟨fun hp' => hp ((reflect_hex ..).1 hp'), reflect i j q,
    (reflect_hex ..).2 hq, reflect_neighbor i j hN⟩

private theorem reflect_missedShape (n : ℤ) (i j : Bool) (p : Site) :
    missedShape n (reflect i j p) ↔ missedShape n p := by
  rcases p with ⟨x,y⟩
  cases i <;> cases j <;> simp [missedShape, reflect, abs_neg] <;> omega

private theorem hasMissed_iff {n : ℤ} (hn : 1 ≤ n) (p : Site) :
    hasMissed n p ↔ missedShape n p := by
  rcases p with ⟨x,y⟩
  let i := decide (x < 0)
  let j := decide (y < 0)
  have hx : 0 ≤ (reflect i j (x,y)).1 := by simp [reflect, i]; split <;> omega
  have hy : 0 ≤ (reflect i j (x,y)).2 := by simp [reflect, j]; split <;> omega
  have h := missed_quadrant hn hx hy
  change hasMissed n (reflect i j (x,y)) ↔ missedShape n (reflect i j (x,y)) at h
  rw [← reflect_missedShape n i j (x,y), ← h]
  exact ⟨reflect_missed n i j _, fun hp => by
    simpa only [reflect_twice] using reflect_missed n i j _ hp⟩

private def missedFin (n : ℤ) : Finset Site :=
  side (n+2) ((n+1)/3) ((n+1)%2) ∪
    (cap (2*n+5) ((n+6)/3) ((2*n+4)/3) false ∪ cap (2*n+5) ((n+6)/3) ((2*n+4)/3) true)

private theorem mem_missedFin {n x y : ℤ} (hn : 1 ≤ n) :
    (x,y) ∈ missedFin n ↔ missedShape n (x,y) := by
  simp only [missedFin, mem_union,
    mem_side (a := n+2) (k := (n+1)/3) (r := (n+1)%2) (by omega),
    mem_cap, Bool.false_eq_true, ite_false, ite_true, missedShape]
  by_cases hx : 0 ≤ x <;> by_cases hy : 0 ≤ y
  all_goals
    have hxa : |x| = if 0 ≤ x then x else -x := by split <;> simp_all [abs_of_neg, abs_of_nonneg]
    have hya : |y| = if 0 ≤ y then y else -y := by split <;> simp_all [abs_of_neg, abs_of_nonneg]
    rw [hxa,hya]
    simp only [hx,hy,ite_true,ite_false]
    constructor
    · rintro (hs | ⟨t, hl, hu, ht, htx⟩ | ⟨t, hl, hu, ht, htx⟩) <;> omega
    · rintro ⟨hp,hs | hc⟩
      · exact Or.inl ⟨by omega, by omega, by omega, by omega⟩
      · right
        first
        | solve | exact Or.inl ⟨y, by omega, by omega, Or.inl rfl, by omega⟩
        | solve | exact Or.inl ⟨-y, by omega, by omega, Or.inr (by omega), by omega⟩
        | solve | exact Or.inr ⟨y, by omega, by omega, Or.inl rfl, by omega⟩
        | exact Or.inr ⟨-y, by omega, by omega, Or.inr (by omega), by omega⟩

private theorem missed_card_eq (n : ℕ) (hn : 1 ≤ n) :
    (missed (shannonHex n) (shannonHex (n+1))).card = (missedFin n).card := by
  have hx (p : Site) : p ∈ missedFin n ↔ hasMissed n p := by
    rcases p with ⟨x,y⟩
    rw [hasMissed_iff (by omega), mem_missedFin (by omega)]
  have hb (c p : Site) : (⟨c,p⟩ : Σ _ : Site, Site) ∈
      missed (shannonHex n) (shannonHex (n+1)) ↔
      c ∈ hex n (2*(n : ℤ)+1) 1 ∧ neighbor p c ∧ p ∉ hex ((n : ℤ)+1) (2*(n : ℤ)+3) 1 := by
    rw [mem_missed]
    simp only [shannonHex, ← mem_coe, coe_hexFin, Nat.cast_succ]
    ring_nf
  apply card_bij (fun p _ => p.2)
  · rintro ⟨c,p⟩ h
    obtain ⟨hc,hN,hp⟩ := (hb c p).1 h
    exact (hx p).2 ⟨hp,c,hc,hN⟩
  · rintro ⟨c,p⟩ h ⟨d,q⟩ h' he
    change p = q at he
    subst q
    obtain ⟨hc,hN,hp⟩ := (hb c p).1 h
    obtain ⟨hd,hN',_⟩ := (hb d p).1 h'
    by_contra hNe
    have hcd : c ≠ d := fun e => hNe (by subst d; rfl)
    rcases p with ⟨x,y⟩
    have hG : (x,y) ∈ grow (hex n (2*(n : ℤ)+1) 1) :=
      Or.inr ⟨c,d,hcd,hN,hN',hc,hd⟩
    have hU := hex_upper (by omega) hG
    apply hp
    simpa only [show 2*(n : ℤ)+1+2 = 2*(n : ℤ)+3 by omega] using hU
  · intro p hp
    obtain ⟨hp,c,hc,hN⟩ := (hx p).1 hp
    exact ⟨⟨c,p⟩, (hb c p).2 ⟨hc,hN,hp⟩, rfl⟩

private theorem missed_card (n : ℕ) (hn : 1 ≤ n) :
    ((missed (shannonHex n) (shannonHex (n+1))).card : ℤ) =
      if (n : ℤ)%3 = 0 then 2*(n : ℤ) else 2*(n : ℤ)+4 := by
  rw [missed_card_eq n hn, missedFin,
    card_rimParts (by omega) (by omega) (by omega) (by omega) (by omega)]
  simp only [Int.card_Icc]
  have hlo : 0 ≤ (n : ℤ)%6 := by omega
  have hhi : (n : ℤ)%6 ≤ 5 := by omega
  interval_cases hmod : (n : ℤ)%6 <;> omega

theorem shannon_edges_one : edgeCount 1 = 6 := by decide

theorem shannon_edges (n : ℕ) (hn : 2 ≤ n) :
    (edgeCount n : ℤ) = 6*(n : ℤ)^2 - 4*(n : ℤ) + (if (n : ℤ)%3 = 2 then 2 else -2) := by
  obtain ⟨m, rfl⟩ : ∃ m : ℕ, n = m+1 := ⟨n-1, by omega⟩
  have hm : 1 ≤ m := by omega
  have hc := shannon_hex_card m hm
  have hl := missed_card m hm
  have he := congrArg (fun z : ℕ => (z : ℤ))
    (arc_add_missed (shannonHex m) (shannonHex (m+1)))
  push_cast at he ⊢
  unfold edgeCount
  rw [show m+1-1 = m by omega, shannon_shape m hm, shannon_shape (m+1) (by omega)]
  have hCalc : (arcCount (shannonHex m) (shannonHex (m+1)) : ℤ) =
      6*(m : ℤ)^2 + 10*(m : ℤ) + 2*correction m -
        (if (m : ℤ)%3 = 0 then 2*(m : ℤ) else 2*(m : ℤ)+4) := by
    linear_combination he + 2*hc - hl
  rw [hCalc]
  have hp : (m : ℤ)%3 = 0 ∨ (m : ℤ)%3 = 1 ∨ (m : ℤ)%3 = 2 := by omega
  rcases hp with h | h | h
  all_goals
    have h' : ((m : ℤ)+1)%3 = (((m : ℤ)%3)+1)%3 := by omega
    rw [h', h]
    simp [correction, h]; ring

def shannonRegionFormula (n : ℤ) : ℤ :=
  if n % 3 = 0 then (15*n^2 - 17*n - 3)/3
  else if n % 3 = 1 then |(15*n^2 - 17*n - 7)/3|
  else (15*n^2 - 17*n + 7)/3

theorem shannon_regions (n : ℕ) (hn : 1 ≤ n) :
    regionCount n = shannonRegionFormula n := by
  by_cases h1 : n = 1
  · subst n
    decide
  have hn' : 2 ≤ n := by omega
  unfold regionCount shannonRegionFormula
  rw [shannon_edges n hn']
  have hv := shannon_hex_card n hn
  rw [← shannon_shape n hn] at hv
  have hR : (n : ℤ)%3 = 0 ∨ (n : ℤ)%3 = 1 ∨ (n : ℤ)%3 = 2 := by omega
  rcases hR with h | h | h
  all_goals simp [correction, h] at hv ⊢
  · have hmul : 3*(6*(n : ℤ)^2 - 4*(n : ℤ) - 2 - (iterate seedShannon n).card + 1) =
        15*(n : ℤ)^2 - 17*(n : ℤ) - 3 := by linear_combination -hv
    omega
  · have hnonneg : 0 ≤ (15*(n : ℤ)^2 - 17*(n : ℤ) - 7)/3 := by
      have ht : (2 : ℤ) ≤ (n : ℤ) := by omega
      have hq : 0 ≤ ((n : ℤ)-2)^2 := sq_nonneg _
      have h' : 0 ≤ 15*(n : ℤ)^2 - 17*(n : ℤ) - 7 := by nlinarith
      omega
    rw [abs_of_nonneg hnonneg]
    have hmul : 3*(6*(n : ℤ)^2 - 4*(n : ℤ) - 2 - (iterate seedShannon n).card + 1) =
        15*(n : ℤ)^2 - 17*(n : ℤ) - 7 := by linear_combination -hv
    omega
  · have hmul : 3*(6*(n : ℤ)^2 - 4*(n : ℤ) + 2 - (iterate seedShannon n).card + 1) =
        15*(n : ℤ)^2 - 17*(n : ℤ) + 7 := by linear_combination -hv
    omega

/-! Géométrie des intersections. En coordonnées réelles (x,y) on plonge le
plan dans ℂ par (x + √3 y i)/2, donc le carré de la distance est
la forme quadratique (x² + 3y²)/4. -/

private theorem center_cases {d e : ℤ} (hd : 0 ≤ d) (he : 0 ≤ e)
    (hne : d ≠ 0 ∨ e ≠ 0) (hP : (d+e)%2 = 0) (hQ : d^2 + 3*e^2 ≤ 16) :
    (d = 0 ∧ e = 2) ∨ (d = 1 ∧ e = 1) ∨ (d = 2 ∧ e = 0) ∨
    (d = 2 ∧ e = 2) ∨ (d = 3 ∧ e = 1) ∨ (d = 4 ∧ e = 0) := by
  have hd' : d ≤ 4 := by
    by_contra! h
    have hm := mul_nonneg (show 0 ≤ d-5 by omega) (show 0 ≤ d+5 by omega)
    nlinarith only [hQ, hm, sq_nonneg e]
  have he' : e ≤ 2 := by
    by_contra! h
    have hm := mul_nonneg (show 0 ≤ e-3 by omega) (show 0 ≤ e+3 by omega)
    nlinarith only [hQ, hm, sq_nonneg d]
  interval_cases e <;> interval_cases d <;> norm_num at *

private theorem intersection_quadrant {d e : ℤ} (hd : 0 ≤ d) (he : 0 ≤ e)
    (hne : d ≠ 0 ∨ e ≠ 0) (hP : (d+e)%2 = 0) {x y : ℝ}
    (h₀ : x^2 + 3*y^2 = 4)
    (h₁ : (x-(d : ℝ))^2 + 3*(y-(e : ℝ))^2 = 4) :
    ∃ u v : ℤ, (u+v)%2 = 0 ∧ (u : ℝ) = x ∧ (v : ℝ) = y := by
  have hBound : (d : ℝ)^2 + 3*(e : ℝ)^2 ≤ 16 := by
    nlinarith only [h₀, h₁, sq_nonneg (2*x-(d : ℝ)), sq_nonneg (2*y-(e : ℝ))]
  have hQ : d^2 + 3*e^2 ≤ 16 := by exact_mod_cast hBound
  have hLine : 2*(d : ℝ)*x + 6*(e : ℝ)*y = (d : ℝ)^2+3*(e : ℝ)^2 := by
    linear_combination h₀-h₁
  rcases center_cases hd he hne hP hQ with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ |
    ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
  all_goals norm_num at hLine
  · have hy : y = 1 := by linarith
    have hxx : x^2 = (1 : ℝ)^2 := by rw [hy] at h₀; linarith
    rcases sq_eq_sq_iff_eq_or_eq_neg.mp hxx with hx | hx
    · exact ⟨1,1,by decide,by simp [hx],by simp [hy]⟩
    · exact ⟨-1,1,by decide,by simp [hx],by simp [hy]⟩
  · have hx : x = 2-3*y := by linarith
    rw [hx] at h₀
    have hroot : y*(y-1) = 0 := by nlinarith only [h₀]
    rcases mul_eq_zero.mp hroot with hy | hy
    · refine ⟨2,0,by decide,?_,by simp [hy]⟩
      norm_num [hx,hy]
    · have hy' : y = 1 := by linarith
      refine ⟨-1,1,by decide,?_,by simp [hy']⟩
      norm_num [hx,hy']
  · have hx : x = 1 := by linarith
    have hyy : y^2 = (1 : ℝ)^2 := by rw [hx] at h₀; linarith
    rcases sq_eq_sq_iff_eq_or_eq_neg.mp hyy with hy | hy
    · exact ⟨1,1,by decide,by simp [hx],by simp [hy]⟩
    · exact ⟨1,-1,by decide,by simp [hx],by simp [hy]⟩
  · have hx : x = 4-3*y := by linarith
    rw [hx] at h₀
    have hroot : (y-1)^2 = 0 := by nlinarith only [h₀]
    have hy : y = 1 := sub_eq_zero.mp (sq_eq_zero_iff.mp hroot)
    refine ⟨1,1,by decide,?_,by simp [hy]⟩
    norm_num [hx,hy]
  · have hx : x = 2-y := by linarith
    rw [hx] at h₀
    have hroot : y*(y-1) = 0 := by nlinarith only [h₀]
    rcases mul_eq_zero.mp hroot with hy | hy
    · refine ⟨2,0,by decide,?_,by simp [hy]⟩
      norm_num [hx,hy]
    · have hy' : y = 1 := by linarith
      exact ⟨1,1,by decide,by norm_num [hx,hy'],by simp [hy']⟩
  · have hx : x = 2 := by linarith
    have hroot : y^2 = 0 := by rw [hx] at h₀; linarith
    exact ⟨2,0,by decide,by simp [hx],by simp [sq_eq_zero_iff.mp hroot]⟩

private theorem scaled_intersection {d e : ℤ} (hne : d ≠ 0 ∨ e ≠ 0) (hP : (d+e)%2 = 0)
    {x y : ℝ} (h₀ : x^2 + 3*y^2 = 4)
    (h₁ : (x-(d : ℝ))^2 + 3*(y-(e : ℝ))^2 = 4) :
    ∃ u v : ℤ, (u+v)%2 = 0 ∧ (u : ℝ) = x ∧ (v : ℝ) = y := by
  by_cases hd : 0 ≤ d <;> by_cases he : 0 ≤ e
  · exact intersection_quadrant hd he hne hP h₀ h₁
  · have hh : (x-(d : ℝ))^2 + 3*(-y-((-e : ℤ) : ℝ))^2 = 4 := by
      push_cast
      linear_combination h₁
    obtain ⟨u,v,hp,hu,hv⟩ := intersection_quadrant hd (show 0 ≤ -e by omega)
      (by omega) (by omega) (by simpa using h₀) hh
    exact ⟨u,-v,by omega,hu,by simp [hv]⟩
  · have hh : (-x-((-d : ℤ) : ℝ))^2 + 3*(y-(e : ℝ))^2 = 4 := by
      push_cast
      linear_combination h₁
    obtain ⟨u,v,hp,hu,hv⟩ := intersection_quadrant (show 0 ≤ -d by omega) he
      (by omega) (by omega) (by simpa using h₀) hh
    exact ⟨-u,v,by omega,by simp [hu],hv⟩
  · have hh : (-x-((-d : ℤ) : ℝ))^2 + 3*(-y-((-e : ℤ) : ℝ))^2 = 4 := by
      push_cast
      linear_combination h₁
    obtain ⟨u,v,hp,hu,hv⟩ := intersection_quadrant (show 0 ≤ -d by omega)
      (show 0 ≤ -e by omega) (by omega) (by omega) (by simpa using h₀) hh
    exact ⟨-u,-v,by omega,by simp [hu],by simp [hv]⟩

/-- Plongement dans le plan, avec les six déplacements à distance unité. -/
noncomputable def toPlane (p : Site) : ℂ :=
  ⟨(p.1 : ℝ)/2, Real.sqrt 3*(p.2 : ℝ)/2⟩

theorem toPlane_injective : Function.Injective toPlane := by
  rintro ⟨u,v⟩ ⟨x,y⟩ he
  have hr := congrArg Complex.re he
  have hi := congrArg Complex.im he
  change (u : ℝ)/2 = (x : ℝ)/2 at hr
  change Real.sqrt 3*(v : ℝ)/2 = Real.sqrt 3*(y : ℝ)/2 at hi
  have hs : 0 < Real.sqrt 3 := Real.sqrt_pos.2 (by norm_num)
  have h1 : (u : ℝ) = (x : ℝ) := by linarith
  have h2 : (v : ℝ) = (y : ℝ) := by
    apply mul_left_cancel₀ hs.ne'
    linarith
  exact Prod.ext (by exact_mod_cast h1) (by exact_mod_cast h2)

private theorem norm_toPlane (z : ℂ) (p : Site) :
    4 * ‖z - toPlane p‖^2 =
      (2*z.re-(p.1 : ℝ))^2 + 3*(2*z.im/Real.sqrt 3-(p.2 : ℝ))^2 := by
  have hs : Real.sqrt 3 ≠ 0 := (Real.sqrt_pos.2 (by norm_num)).ne'
  have hs2 : (Real.sqrt 3)^2 = 3 := Real.sq_sqrt (by norm_num)
  rw [Complex.sq_norm, Complex.normSq_apply]
  simp only [Complex.sub_re, Complex.sub_im, toPlane]
  have hre : z.re-(p.1 : ℝ)/2 = (2*z.re-(p.1 : ℝ))/2 := by ring
  have him : z.im-Real.sqrt 3*(p.2 : ℝ)/2 =
      (Real.sqrt 3/2)*(2*z.im/Real.sqrt 3-(p.2 : ℝ)) := by
    field_simp [hs]
  rw [hre, him]
  calc
    _ = (2*z.re-(p.1 : ℝ))^2 +
        (Real.sqrt 3)^2*(2*z.im/Real.sqrt 3-(p.2 : ℝ))^2 := by ring
    _ = _ := by rw [hs2]

theorem circle_intersections_on_lattice (p q : Site)
    (hpar : (p.1+p.2)%2 = (q.1+q.2)%2) (hne : p ≠ q) {z : ℂ}
    (hp : ‖z-toPlane p‖ = 1) (hq : ‖z-toPlane q‖ = 1) :
    ∃ r : Site, (r.1+r.2)%2 = (p.1+p.2)%2 ∧ toPlane r = z := by
  rcases p with ⟨a,b⟩
  rcases q with ⟨c,d⟩
  change (a+b)%2 = (c+d)%2 at hpar
  have hs : Real.sqrt 3 ≠ 0 := (Real.sqrt_pos.2 (by norm_num)).ne'
  have h₀ := norm_toPlane z (a,b)
  have h₁ := norm_toPlane z (c,d)
  rw [hp] at h₀
  rw [hq] at h₁
  have hne' : c-a ≠ 0 ∨ d-b ≠ 0 := by
    by_contra! hh
    apply hne
    exact Prod.ext (by omega) (by omega)
  obtain ⟨u,v,hP,hu,hv⟩ := scaled_intersection hne' (by omega)
    (x := 2*z.re-(a : ℝ)) (y := 2*z.im/Real.sqrt 3-(b : ℝ))
    (by linarith only [h₀]) (by push_cast; linear_combination -h₁)
  refine ⟨(u+a,v+b), by dsimp; omega, ?_⟩
  apply Complex.ext
  · change ((↑(u+a) : ℝ)/2) = z.re
    push_cast
    linarith
  · change Real.sqrt 3*(↑(v+b) : ℝ)/2 = z.im
    push_cast
    field_simp [hs] at hv
    linear_combination hv / 2

private theorem norm_lattice (p q : Site) :
    4 * ‖toPlane q - toPlane p‖^2 =
      ((q.1 : ℝ)-(p.1 : ℝ))^2 + 3*((q.2 : ℝ)-(p.2 : ℝ))^2 := by
  have hs : Real.sqrt 3 ≠ 0 := (Real.sqrt_pos.2 (by norm_num)).ne'
  have hi : 2*(Real.sqrt 3*(q.2 : ℝ)/2)/Real.sqrt 3 = (q.2 : ℝ) := by
    field_simp [hs]
  rw [norm_toPlane]
  change (2*((q.1 : ℝ)/2)-(p.1 : ℝ))^2 +
    3*(2*(Real.sqrt 3*(q.2 : ℝ)/2)/Real.sqrt 3-(p.2 : ℝ))^2 = _
  rw [hi]
  ring

private theorem unit_cases {d e : ℤ} (h : d^2 + 3*e^2 = 4) :
    (d=2 ∧ e=0) ∨ (d=-2 ∧ e=0) ∨ (d=1 ∧ e=1) ∨ (d=-1 ∧ e=1) ∨
    (d=1 ∧ e=-1) ∨ (d=-1 ∧ e=-1) := by
  have hd : -2 ≤ d ∧ d ≤ 2 := by
    constructor
    · by_contra! h'
      have hm := mul_nonneg (show 0 ≤ -d-3 by omega) (show 0 ≤ -d+3 by omega)
      nlinarith only [h, hm, sq_nonneg e]
    · by_contra! h'
      have hm := mul_nonneg (show 0 ≤ d-3 by omega) (show 0 ≤ d+3 by omega)
      nlinarith only [h, hm, sq_nonneg e]
  have he : -1 ≤ e ∧ e ≤ 1 := by
    constructor
    · by_contra! h'
      have hm := mul_nonneg (show 0 ≤ -e-2 by omega) (show 0 ≤ -e+2 by omega)
      nlinarith only [h, hm, sq_nonneg d]
    · by_contra! h'
      have hm := mul_nonneg (show 0 ≤ e-2 by omega) (show 0 ≤ e+2 by omega)
      nlinarith only [h, hm, sq_nonneg d]
  obtain ⟨_,_⟩ := hd
  obtain ⟨_,_⟩ := he
  interval_cases e <;> interval_cases d <;> norm_num at *

theorem neighbor_iff_unit_distance (p q : Site) :
    neighbor p q ↔ ‖toPlane q - toPlane p‖ = 1 := by
  rcases p with ⟨a,b⟩
  rcases q with ⟨c,d⟩
  have h := norm_lattice (a,b) (c,d)
  change 4*‖toPlane (c,d)-toPlane (a,b)‖^2 =
    ((c : ℝ)-(a : ℝ))^2+3*((d : ℝ)-(b : ℝ))^2 at h
  constructor
  · intro hn
    have hn' : (c-a)^2+3*(d-b)^2 = 4 := by
      simp only [neighbor, shift, Prod.mk.injEq] at hn
      rcases hn with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ |
        ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ <;> ring
    have hr : ((c : ℝ)-(a : ℝ))^2+3*((d : ℝ)-(b : ℝ))^2 = 4 := by exact_mod_cast hn'
    rw [hr] at h
    have hh : ‖toPlane (c,d)-toPlane (a,b)‖^2 = (1 : ℝ)^2 := by linarith
    rcases sq_eq_sq_iff_eq_or_eq_neg.mp hh with he | he
    · exact he
    · linarith [norm_nonneg (toPlane (c,d)-toPlane (a,b))]
  · intro hu
    rw [hu] at h
    have hr : ((c : ℝ)-(a : ℝ))^2+3*((d : ℝ)-(b : ℝ))^2 = 4 := by linarith
    have hQ : (c-a)^2+3*(d-b)^2 = 4 := by exact_mod_cast hr
    have hc := unit_cases hQ
    simp only [neighbor, shift, Prod.mk.injEq]
    omega

/-- Un tour de la construction géométrique, avec conservation des sommets déjà présents. -/
def circleStep (S : Set ℂ) : Set ℂ :=
  S ∪ {z | ∃ c ∈ S, ∃ d ∈ S, c ≠ d ∧ ‖z-c‖ = 1 ∧ ‖z-d‖ = 1}

theorem circleStep_image (S : Set Site)
    (hParity : ∀ p ∈ S, ∀ q ∈ S, (p.1+p.2)%2 = (q.1+q.2)%2) :
    circleStep (toPlane '' S) = toPlane '' grow S := by
  ext z
  constructor
  · rintro (hz | ⟨c, ⟨p,hp,rfl⟩, d, ⟨q,hq,rfl⟩, hne, hc, hd⟩)
    · obtain ⟨p,hp,rfl⟩ := hz
      exact ⟨p,Or.inl hp,rfl⟩
    · have hne' : p ≠ q := fun h => hne (congrArg toPlane h)
      obtain ⟨r,_,rfl⟩ := circle_intersections_on_lattice p q (hParity p hp q hq) hne' hc hd
      exact ⟨r, Or.inr ⟨p,q,hne',
        neighbor_symm ((neighbor_iff_unit_distance p r).2 hc),
        neighbor_symm ((neighbor_iff_unit_distance q r).2 hd),hp,hq⟩, rfl⟩
  · rintro ⟨r, hr, rfl⟩
    rcases hr with hr | ⟨p,q,hne,hp,hq,hpS,hqS⟩
    · exact Or.inl ⟨r,hr,rfl⟩
    · exact Or.inr ⟨toPlane p, ⟨p,hpS,rfl⟩, toPlane q, ⟨q,hqS,rfl⟩,
        fun e => hne (toPlane_injective e),
        (neighbor_iff_unit_distance p r).1 (neighbor_symm hp),
        (neighbor_iff_unit_distance q r).1 (neighbor_symm hq)⟩

private theorem neighbor_parity {p q : Site} (h : neighbor p q) :
    (p.1+p.2)%2 = (q.1+q.2)%2 := by
  rcases p with ⟨x,y⟩
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl <;> simp only [shift] <;> omega

theorem geometric_iterate (S : Finset Site) (n : ℕ) (s : ℤ)
    (hs : ∀ p ∈ S, (p.1+p.2)%2 = s) :
    (circleStep^[n]) (toPlane '' (S : Set Site)) = toPlane '' (iterate S n : Set Site) ∧
      ∀ p ∈ iterate S n, (p.1+p.2)%2 = s := by
  induction n with
  | zero => exact ⟨rfl,hs⟩
  | succ n ih =>
    rw [Function.iterate_succ_apply', ih.1, iterate_succ, coe_growFin]
    constructor
    · apply circleStep_image
      intro p hp q hq
      exact (ih.2 p hp).trans (ih.2 q hq).symm
    · intro p hp
      rw [← mem_coe, coe_growFin] at hp
      rcases hp with hp | ⟨q,_,_,hN,_,hq,_⟩
      · exact ih.2 p hp
      · exact (neighbor_parity hN).trans (ih.2 q hq)

theorem shannon_geometric_vertices (n : ℕ) (hn : 1 ≤ n) :
    (((circleStep^[n]) (toPlane '' (seedShannon : Set Site))).ncard : ℤ) =
      (3*(n : ℤ)^2 + 5*(n : ℤ) + correction n)/3 := by
  have hp : ∀ p ∈ seedShannon, (p.1+p.2)%2 = 1 := by
    intro p hp
    simp [seedShannon] at hp
    rcases hp with rfl | rfl <;> decide
  rw [(geometric_iterate seedShannon n 1 hp).1, Set.ncard_image_of_injective _ toPlane_injective,
    Set.ncard_coe_finset]
  exact shannon_vertices n hn

theorem markey_initial : (iterate seedMarkey 0).card = 5 ∧
    (iterate seedMarkey 1).card = 13 := by decide

theorem markey_difference (n : ℕ) (hn : 2 ≤ n) :
    ((iterate seedMarkey n).card : ℤ) =
      (iterate seedShannon n).card + 4*(n : ℤ) + 7 := by
  rw [markey_shape n hn, shannon_shape n (by omega)]
  exact markey_hex_difference n hn

#print axioms grow_hex
#print axioms shannon_shape
#print axioms markey_shape
#print axioms shannon_vertices
#print axioms markey_vertices
#print axioms markey_initial
#print axioms markey_difference
#print axioms shannon_edges_one
#print axioms shannon_edges
#print axioms shannon_regions
#print axioms circle_intersections_on_lattice
#print axioms shannon_geometric_vertices

end Cercles
