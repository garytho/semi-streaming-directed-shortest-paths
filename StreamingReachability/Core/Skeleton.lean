module

public import StreamingReachability.Core.TopRows
public import StreamingReachability.Core.MultiSource
public import StreamingReachability.Core.Certificates

@[expose] public section

namespace StreamingReachability.Core

namespace Skeleton

open StoredEdges

variable {n : ℕ}

def key (e : Edge n) : ℕ := e.weight * n + e.target.val

theorem key_mod (_hn : 0 < n) (e : Edge n) : key e % n = e.target.val := by
  simp [key, Nat.add_mod, Nat.mod_eq_of_lt e.target.isLt]

theorem key_div (hn : 0 < n) (e : Edge n) : key e / n = e.weight := by
  rw [key, Nat.mul_comm e.weight n, Nat.mul_add_div hn]
  simp [Nat.div_eq_of_lt e.target.isLt]

def eligible (B known : Finset (Fin n)) (a : Fin n) (e : Edge n) : Prop :=
  e.source = a ∧ e.target ∈ B ∧ e.target ∉ known
  deriving Decidable

def keys (B known : Finset (Fin n)) (a : Fin n) (edges : List (Edge n)) : List ℕ :=
  edges.filterMap fun e => if eligible B known a e then some (key e) else none

theorem mem_keys (B known : Finset (Fin n)) (a : Fin n)
    (edges : List (Edge n)) (k : ℕ) :
    k ∈ keys B known a edges ↔
      ∃ e ∈ edges, eligible B known a e ∧ key e = k := by
  simp only [keys, List.mem_filterMap]
  constructor
  · rintro ⟨e, he, hk⟩
    split_ifs at hk with hel
    · exact ⟨e, he, hel, Option.some.inj hk⟩
  · rintro ⟨e, he, hel, rfl⟩
    exact ⟨e, he, by simp [hel]⟩

structure Row (n : ℕ) where
  source : Fin n
  kept : Finset ℕ
  deriving DecidableEq

def updateRow (B known : Finset (Fin n)) (τ : ℕ) (e : Edge n) (row : Row n) : Row n :=
  { source := row.source
    kept := if eligible B known row.source e
      then TopRows.offer n τ (key e) row.kept else row.kept }

def finishRow (B known : Finset (Fin n)) (τ : ℕ) :
    List (Edge n) → Row n → Row n
  | [], row => row
  | e :: es, row => finishRow B known τ es (updateRow B known τ e row)

def scanRows (B known : Finset (Fin n)) (τ : ℕ) :
    List (Edge n) → List (Row n) → List (Row n)
  | [], rows => rows
  | e :: es, rows => scanRows B known τ es (rows.map (updateRow B known τ e))

theorem scanRows_eq_map (B known : Finset (Fin n)) (τ : ℕ)
    (edges : List (Edge n)) (rows : List (Row n)) :
    scanRows B known τ edges rows = rows.map (finishRow B known τ edges) := by
  induction edges generalizing rows with
  | nil => simp [scanRows, finishRow]
  | cons e es ih =>
      simp only [scanRows, ih, List.map_map, Function.comp_def, finishRow]

theorem finishRow_eq (B known : Finset (Fin n)) (τ : ℕ)
    (edges : List (Edge n)) (a : Fin n) (row : Finset ℕ) :
    finishRow B known τ edges ⟨a, row⟩ =
      ⟨a, (keys B known a edges).foldl (fun r k => TopRows.offer n τ k r) row⟩ := by
  induction edges generalizing row with
  | nil => rfl
  | cons e es ih =>
      simp only [finishRow, updateRow, keys, List.filterMap_cons]
      by_cases hel : eligible B known a e
      · simpa only [hel, ↓reduceIte, List.foldl_cons, keys] using
          ih (TopRows.offer n τ (key e) row)
      · simpa only [hel, ↓reduceIte, keys] using ih row

def rows (B known : Finset (Fin n)) (τ : ℕ) (edges : List (Edge n)) : List (Row n) :=
  scanRows B known τ edges ((B.sort (· ≤ ·)).map fun a => ⟨a, ∅⟩)

theorem rows_eq (B known : Finset (Fin n)) (τ : ℕ) (edges : List (Edge n)) :
    rows B known τ edges =
      (B.sort (· ≤ ·)).map fun a => Row.mk a (TopRows.build n τ (keys B known a edges)) := by
  simp only [rows, scanRows_eq_map, List.map_map, Function.comp_def, finishRow_eq,
    TopRows.build]

theorem row_mem (B known : Finset (Fin n)) (τ : ℕ) (edges : List (Edge n)) (a : Fin n)
    (ha : a ∈ B) :
    Row.mk a (TopRows.build n τ (keys B known a edges)) ∈ rows B known τ edges := by
  rw [rows_eq]
  exact List.mem_map.mpr ⟨a, (Finset.mem_sort _).mpr ha, rfl⟩

def decode (hn : 0 < n) (a : Fin n) (k : ℕ) : Edge n :=
  ⟨a, ⟨k % n, Nat.mod_lt _ hn⟩, k / n⟩

theorem decode_key (hn : 0 < n) (e : Edge n) :
    decode hn e.source (key e) = e := by
  have ht : (decode hn e.source (key e)).target = e.target := Fin.ext (key_mod hn e)
  have hw : (decode hn e.source (key e)).weight = e.weight := key_div hn e
  cases e
  simp only [decode, Edge.mk.injEq, true_and] at *
  exact ⟨ht, hw⟩

theorem key_decode (hn : 0 < n) (a : Fin n) (k : ℕ) :
    key (decode hn a k) = k := by
  change k / n * n + k % n = k
  simpa only [Nat.mul_comm] using Nat.div_add_mod k n

def rowEdges (hn : 0 < n) (row : Row n) : List (Edge n) :=
  (row.kept.sort (· ≤ ·)).map (decode hn row.source)

def build (hn : 0 < n) (B known : Finset (Fin n)) (τ : ℕ)
    (edges : List (Edge n)) : List (Edge n) :=
  (rows B known τ edges).flatMap (rowEdges hn)

theorem decode_mem_build (hn : 0 < n) (B known : Finset (Fin n)) (τ : ℕ)
    (edges : List (Edge n)) {a : Fin n} (ha : a ∈ B) {k : ℕ}
    (hk : k ∈ TopRows.build n τ (keys B known a edges)) :
    decode hn a k ∈ build hn B known τ edges := by
  apply List.mem_flatMap.mpr
  refine ⟨_, row_mem B known τ edges a ha, ?_⟩
  exact List.mem_map.mpr ⟨k, (Finset.mem_sort _).mpr hk, rfl⟩

theorem retained (hn : 0 < n) (B known : Finset (Fin n)) (τ : ℕ)
    (edges : List (Edge n)) {e : Edge n} (he : e ∈ build hn B known τ edges) :
    e ∈ edges ∧ e.source ∈ B ∧ e.target ∈ B ∧ e.target ∉ known := by
  obtain ⟨row, hr, hk⟩ := List.mem_flatMap.mp he
  rw [rows_eq] at hr
  obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hr
  unfold rowEdges at hk
  obtain ⟨k, hkm, heq⟩ := List.mem_map.mp hk
  subst e
  have hvalid := TopRows.build_valid n τ (keys B known a edges)
  have hseen := List.mem_toFinset.mp (hvalid.retained ((Finset.mem_sort _).mp hkm))
  obtain ⟨e, heSeen, hel, hkey⟩ := (mem_keys B known a edges k).mp hseen
  obtain ⟨hs, htB, htK⟩ := hel
  subst k
  subst a
  simpa only [decode_key] using And.intro heSeen
    (And.intro ((Finset.mem_sort _).mp ha) (And.intro htB htK))

theorem graph_subgraph (hn : 0 < n) (B known : Finset (Fin n)) (τ : ℕ)
    (edges : List (Edge n)) (u v : Fin n) :
    graphOfEdges edges u v ≤ graphOfEdges (build hn B known τ edges) u v :=
  graphOfEdges_antitone (fun _ he => (retained hn B known τ edges he).1) u v

theorem retained_key (hn : 0 < n) (B known : Finset (Fin n)) (τ : ℕ)
    (edges : List (Edge n)) {e : Edge n} (he : e ∈ build hn B known τ edges) :
    key e ∈ TopRows.build n τ (keys B known e.source edges) := by
  obtain ⟨row, hr, hrow⟩ := List.mem_flatMap.mp he
  rw [rows_eq] at hr
  obtain ⟨a, _, rfl⟩ := List.mem_map.mp hr
  unfold rowEdges at hrow
  obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hrow
  change key (decode hn a k) ∈ TopRows.build n τ (keys B known a edges)
  rw [key_decode]
  exact (Finset.mem_sort (· ≤ ·)).mp hk

theorem retained_minimum (hn : 0 < n) (B known : Finset (Fin n)) (τ : ℕ)
    (edges : List (Edge n)) {e f : Edge n} (he : e ∈ build hn B known τ edges)
    (hf : f ∈ edges) (hs : f.source = e.source) (ht : f.target = e.target) :
    e.weight ≤ f.weight := by
  have hr := retained hn B known τ edges he
  have hseen : key f ∈ (keys B known e.source edges).toFinset :=
    List.mem_toFinset.mpr ((mem_keys _ _ _ _ _).mpr
      ⟨f, hf, ⟨hs, ht ▸ hr.2.2.1, ht ▸ hr.2.2.2⟩, rfl⟩)
  have hkey := TopRows.retained_minimum n τ _ _
    (TopRows.build_valid n τ (keys B known e.source edges))
    (retained_key hn B known τ edges he) hseen
    (by rw [key_mod hn e, key_mod hn f, ht])
  simpa only [key_div hn e, key_div hn f] using Nat.div_le_div_right (c := n) hkey

theorem length_le (hn : 0 < n) (B known : Finset (Fin n)) (τ : ℕ)
    (edges : List (Edge n)) :
    (build hn B known τ edges).length ≤ B.card * τ := by
  unfold build
  rw [rows_eq, List.flatMap_map]
  calc
    ((B.sort (· ≤ ·)).flatMap (fun a =>
      rowEdges hn ⟨a, TopRows.build n τ (keys B known a edges)⟩)).length
        = ((B.sort (· ≤ ·)).map fun a =>
          (TopRows.build n τ (keys B known a edges)).card).sum := by
            simp [List.length_flatMap, rowEdges]
    _ ≤ ((B.sort (· ≤ ·)).map fun _ => τ).sum := by
      have hsum (as : List (Fin n)) :
          (as.map fun a => (TopRows.build n τ (keys B known a edges)).card).sum ≤
            (as.map fun _ => τ).sum := by
        induction as with
        | nil => exact le_rfl
        | cons a as ih =>
            simpa only [List.map_cons, List.sum_cons] using
              Nat.add_le_add (TopRows.build_valid n τ (keys B known a edges)).bounded ih
      exact hsum _
    _ = B.card * τ := by simp

theorem outgoing (hn : 0 < n) (B known : Finset (Fin n)) (τ : ℕ)
    (edges : List (Edge n)) {e : Edge n} (he : e ∈ edges)
    (ha : e.source ∈ B) (hb : e.target ∈ B) (hk : e.target ∉ known) :
    graphOfEdges (build hn B known τ edges) e.source e.target ≤ (e.weight : Distance) ∨
      ∃ Z : Finset (Fin n), Z ⊆ B \ known ∧ Z.card = τ ∧
        ∀ z ∈ Z, graphOfEdges (build hn B known τ edges) e.source z ≤
          (e.weight : Distance) := by
  let row := TopRows.build n τ (keys B known e.source edges)
  have hv : TopRows.Valid n τ (keys B known e.source edges).toFinset row :=
    TopRows.build_valid n τ _
  have hseen : key e ∈ (keys B known e.source edges).toFinset :=
    List.mem_toFinset.mpr ((mem_keys _ _ _ _ _).mpr ⟨e, he, ⟨rfl, hb, hk⟩, rfl⟩)
  rcases hv.covers (key e) hseen with ⟨q, hq, hr, hqle⟩ | hlow
  · left
    have hmem := decode_mem_build hn B known τ edges ha hq
    have heq : (decode hn e.source q).target = e.target := by
      apply Fin.ext
      exact hr.trans (key_mod hn e)
    have hw : q / n ≤ e.weight := by
      simpa only [key_div hn e] using (Nat.div_le_div_right (c := n) hqle)
    have hg := (graphOfEdges_le_edge _ hmem).trans (WithTop.coe_le_coe.mpr hw)
    change graphOfEdges _ e.source (decode hn e.source q).target ≤ _ at hg
    rwa [heq] at hg
  · right
    let Q := row.filter (· ≤ key e)
    have hQ : Q.card = τ :=
      le_antisymm ((Finset.card_filter_le _ _).trans hv.bounded) hlow
    let target : ℕ → Fin n := fun q => ⟨q % n, Nat.mod_lt _ hn⟩
    refine ⟨Q.image target, ?_, ?_, ?_⟩
    · intro z hz
      obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hz
      have hqr := (Finset.mem_filter.mp hq).1
      have hmem := decode_mem_build hn B known τ edges ha hqr
      have hm := retained hn B known τ edges hmem
      exact Finset.mem_sdiff.mpr ⟨hm.2.2.1, hm.2.2.2⟩
    · rw [Finset.card_image_iff.mpr, hQ]
      intro a ha b hb heq
      exact hv.unique a (Finset.mem_filter.mp ha).1 b (Finset.mem_filter.mp hb).1
        (congrArg Fin.val heq)
    · intro z hz
      obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hz
      obtain ⟨hqr, hqle⟩ := Finset.mem_filter.mp hq
      have hw : q / n ≤ e.weight := by
        simpa only [key_div hn e] using (Nat.div_le_div_right (c := n) hqle)
      exact (graphOfEdges_le_edge _
        (decode_mem_build hn B known τ edges ha hqr)).trans (WithTop.coe_le_coe.mpr hw)

end Skeleton

end StreamingReachability.Core
