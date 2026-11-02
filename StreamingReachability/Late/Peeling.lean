module

public import StreamingReachability.Late.Routes

@[expose] public section

namespace StreamingReachability.Late

open scoped Classical BigOperators
open Early Implicit

noncomputable section

variable {n : ℕ} {R : Representation n} {G : Graph (Fin n)}
variable {s t u : Fin n}

structure Frame (R : Representation n) (G : Graph (Fin n)) (F : Graph (Fin n))
    (S X : Finset (Fin n)) (A : ℕ) (D : ℝ) {s t : Fin n} (Q : Path R G s t) where
  first : Fin n
  last : Fin n
  middle : Path R G first last
  inside : middle.Inside S
  vertices_inside : ∀ z ∈ middle.vertices, z ∈ X
  short : (middle.searchWeight A : ℝ) ≤ D
  edges_sublist : middle.edges.Sublist Q.edges
  leftBudget : ℕ
  rightBudget : ℕ
  left : Route F s first leftBudget
  right : Route F last t rightBudget
  budget : leftBudget + middle.micro + rightBudget ≤ Q.micro
  hops : left.hops + right.hops ≤ 4

def PeelResult (R : Representation n) (G : Graph (Fin n)) (F : Graph (Fin n))
    (S X : Finset (Fin n)) (A : ℕ) (D : ℝ) {s t : Fin n} (Q : Path R G s t) : Prop :=
  (∃ P : Route F s t Q.micro, P.hops ≤ 3) ∨
    Nonempty (Frame R G F S X A D Q)

theorem peel_no_in_tail (Q : Path R G s t) (A : ℕ) (hA : 0 < A)
    (S P : Finset (Fin n)) (rho : Fin n → ℝ) (D : ℝ)
    (F : Graph (Fin n)) (hF : ∀ u v, F u v ≤ R.graph G u v)
    (hblocks : ∀ p ∈ P, ∀ u v, F u v ≤
      closure (R.base G) (block (rounded A (R.restricted G S)) S p (rho p) D) u v)
    {v : Fin n} (Tail : Path R G v t) (hTail : Tail.Inside S)
    (hshort : (Tail.searchWeight A : ℝ) ≤ D)
    (hno : ∀ z ∈ Tail.vertices, ¬ ∃ p ∈ P, Within (rounded A (R.restricted G S)) z p (rho p))
    (hsub : Tail.edges.Sublist Q.edges) (L : ℕ) (left : Route F s v L)
    (hleft : left.hops ≤ 2) (hbudget : L + Tail.micro ≤ Q.micro) :
    PeelResult R G F S (emptyChild (rounded A (R.restricted G S)) S P rho) A D Q := by
  let H := rounded A (R.restricted G S)
  let Out := fun z => ∃ p ∈ P, Within H p z (rho p)
  obtain ⟨hit⟩ := first_hit Tail Out
  cases hit with
  | head Tail hh =>
      obtain ⟨p, hp, hh⟩ := hh
      let right := suffixRoute Tail A hA S hTail p (rho p) D hshort hh F (hblocks p hp)
      have hr : right.hops ≤ 1 := suffixRoute_hops _ _ _ _ _ _ _ _ _ _ _ _
      refine Or.inl ⟨(left.append right).weaken hbudget, ?_⟩
      have h := left.hops_append right
      simp only [Route.hops_weaken]
      omega
  | absent Tail hnone =>
      refine Or.inr ⟨{
        first := v
        last := t
        middle := Tail
        inside := hTail
        vertices_inside := ?_
        short := hshort
        edges_sublist := hsub
        leftBudget := L
        rightBudget := 0
        left := left
        right := Route.nil t
        budget := by simpa using hbudget
        hops := by simpa using hleft.trans (by decide : 2 ≤ 4) }⟩
      intro z hz
      apply (mem_emptyChild _ _ _ _ _).mpr
      refine ⟨Tail.vertices_inside hTail z hz, fun p hp => ⟨?_, ?_⟩⟩
      · exact fun h => hno z hz ⟨p, hp, h⟩
      · exact fun h => hnone z hz ⟨p, hp, h⟩
  | @later _ a b Mid e Rest hMid hh =>
      obtain ⟨hMidS, heRest⟩ := (Mid.inside_append (.cons e Rest)).mp hTail
      obtain ⟨heS, hRestS⟩ := (Path.inside_cons e Rest).mp heRest
      have hRestShort : (Rest.searchWeight A : ℝ) ≤ D := by
        have h0 : (0 : ℝ) ≤ Mid.searchWeight A := Nat.cast_nonneg _
        have h1 : (0 : ℝ) ≤ e.searchWeight A := Nat.cast_nonneg _
        simp only [Path.searchWeight_append, Path.searchWeight, Nat.cast_add] at hshort
        linarith
      obtain ⟨p, hp, hh⟩ := hh
      let close := suffixRoute Rest A hA S hRestS p (rho p) D hRestShort hh F (hblocks p hp)
      let edge := Route.edge _ _ e.micro ((hF _ _).trans_eq e.weight)
      let right := edge.append close
      have hc : close.hops ≤ 1 := suffixRoute_hops _ _ _ _ _ _ _ _ _ _ _ _
      have hr : right.hops ≤ 2 := by
        have h := edge.hops_append close
        have he : edge.hops = 1 := rfl
        dsimp only [right]
        omega
      refine Or.inr ⟨{
        first := v
        last := _
        middle := Mid
        inside := hMidS
        vertices_inside := ?_
        short := ?_
        edges_sublist := (Mid.edges_sublist_left (.cons e Rest)).trans hsub
        leftBudget := L
        rightBudget := e.micro + Rest.micro
        left := left
        right := right
        budget := ?_
        hops := by omega }⟩
      · intro z hz
        apply (mem_emptyChild _ _ _ _ _).mpr
        refine ⟨Mid.vertices_inside hMidS z hz, fun p hp => ⟨?_, ?_⟩⟩
        · exact fun h => hno z (Mid.mem_vertices_append_left (.cons e Rest) hz) ⟨p, hp, h⟩
        · exact fun h => hMid z hz ⟨p, hp, h⟩
      · simp only [Path.searchWeight_append, Path.searchWeight, Nat.cast_add] at hshort
        have h0 : (0 : ℝ) ≤ e.searchWeight A := Nat.cast_nonneg _
        have h1 : (0 : ℝ) ≤ Rest.searchWeight A := Nat.cast_nonneg _
        linarith
      · simpa only [Path.micro_append, Path.micro, add_assoc] using hbudget

theorem overlap_shortcut (P₁ : Path R G s u) {v : Fin n}
    (P₂ : Path R G u v) (P₃ : Path R G v t)
    (A : ℕ) (hA : 0 < A) (S : Finset (Fin n)) (p q : Fin n)
    (rhoP rhoQ D : ℝ) (hS : (P₁.append (P₂.append P₃)).Inside S)
    (hshort : ((P₁.append (P₂.append P₃)).searchWeight A : ℝ) ≤ D)
    (hin : Within (rounded A (R.restricted G S)) v p rhoP)
    (hout : Within (rounded A (R.restricted G S)) q u rhoQ)
    (F : Graph (Fin n))
    (hP : ∀ a b, F a b ≤ closure (R.base G)
      (block (rounded A (R.restricted G S)) S p rhoP D) a b)
    (hQ : ∀ a b, F a b ≤ closure (R.base G)
      (block (rounded A (R.restricted G S)) S q rhoQ D) a b) :
    ∃ T : Route F s t (P₁.append (P₂.append P₃)).micro, T.hops ≤ 2 := by
  have hparts := (P₁.inside_append (P₂.append P₃)).mp hS
  have h₂₃ := (P₂.inside_append P₃).mp hparts.2
  have h₁₂ : (P₁.append P₂).Inside S := (P₁.inside_append P₂).mpr ⟨hparts.1, h₂₃.1⟩
  have hshort₁₂ : ((P₁.append P₂).searchWeight A : ℝ) ≤ D := by
    simp only [Path.searchWeight_append, Nat.cast_add] at *
    have h0 : (0 : ℝ) ≤ P₃.searchWeight A := Nat.cast_nonneg _
    linarith
  have hshort₂₃ : ((P₂.append P₃).searchWeight A : ℝ) ≤ D := by
    simp only [Path.searchWeight_append, Nat.cast_add] at *
    have h0 : (0 : ℝ) ≤ P₁.searchWeight A := Nat.cast_nonneg _
    linarith
  have hB := prefix_support_in_block (P₁.append P₂) A hA S h₁₂ p rhoP D hshort₁₂ hin
  let left := closureRoute P₁ F _ ((P₁.inside_append P₂).mp hB).1 hP
  let right := suffixRoute (P₂.append P₃) A hA S hparts.2 q rhoQ D hshort₂₃ hout F hQ
  have hl : left.hops ≤ 1 := closureRoute_hops _ _ _ _ _
  have hr : right.hops ≤ 1 := suffixRoute_hops _ _ _ _ _ _ _ _ _ _ _ _
  refine ⟨(left.append right).weaken (by simp only [Path.micro_append]; exact le_rfl), ?_⟩
  have h := left.hops_append right
  simp only [Route.hops_weaken]
  omega

/-- Last in-ball index and first out-ball index, with the overlap case stopped
immediately. All nonterminal pieces enter the unique empty-label child. -/
theorem local_peeling (Q : Path R G s t) (A : ℕ) (hA : 0 < A)
    (S P : Finset (Fin n)) (hS : Q.Inside S) (rho : Fin n → ℝ) (D : ℝ)
    (hshort : (Q.searchWeight A : ℝ) ≤ D)
    (F : Graph (Fin n)) (hF : ∀ u v, F u v ≤ R.graph G u v)
    (hblocks : ∀ p ∈ P, ∀ u v, F u v ≤
      closure (R.base G) (block (rounded A (R.restricted G S)) S p (rho p) D) u v) :
    PeelResult R G F S (emptyChild (rounded A (R.restricted G S)) S P rho) A D Q := by
  let H := rounded A (R.restricted G S)
  let In := fun z => ∃ p ∈ P, Within H z p (rho p)
  let Out := fun z => ∃ p ∈ P, Within H p z (rho p)
  obtain ⟨hit⟩ := last_hit Q In
  cases hit with
  | finish Q hh =>
      obtain ⟨p, hp, hh⟩ := hh
      refine Or.inl ⟨prefixRoute Q A hA S hS p (rho p) D hshort hh F (hblocks p hp), ?_⟩
      exact (prefixRoute_hops _ _ _ _ _ _ _ _ _ _ _ _).trans (by decide : 1 ≤ 3)
  | absent Q hnone =>
      exact peel_no_in_tail Q A hA S P rho D F hF hblocks Q hS hshort hnone
        (List.Sublist.refl _) 0 (Route.nil s) (by simp) (by simp)
  | before Pre e Tail hh hTail =>
      obtain ⟨hPreS, heTail⟩ := (Pre.inside_append (.cons e Tail)).mp hS
      obtain ⟨heS, hTailS⟩ := (Path.inside_cons e Tail).mp heTail
      have hPreShort : (Pre.searchWeight A : ℝ) ≤ D := by
        simp only [Path.searchWeight_append, Path.searchWeight, Nat.cast_add] at hshort
        have h0 : (0 : ℝ) ≤ e.searchWeight A := Nat.cast_nonneg _
        have h1 : (0 : ℝ) ≤ Tail.searchWeight A := Nat.cast_nonneg _
        linarith
      have hTailShort : (Tail.searchWeight A : ℝ) ≤ D := by
        simp only [Path.searchWeight_append, Path.searchWeight, Nat.cast_add] at hshort
        have h0 : (0 : ℝ) ≤ Pre.searchWeight A := Nat.cast_nonneg _
        have h1 : (0 : ℝ) ≤ e.searchWeight A := Nat.cast_nonneg _
        linarith
      obtain ⟨p, hp, hh⟩ := hh
      obtain ⟨outHit⟩ := first_hit Pre Out
      cases outHit with
      | head Pre hout =>
          obtain ⟨q, hq, hout⟩ := hout
          let T := suffixRoute (Pre.append (.cons e Tail)) A hA S hS q (rho q) D
            hshort hout F (hblocks q hq)
          exact Or.inl ⟨T, (suffixRoute_hops _ _ _ _ _ _ _ _ _ _ _ _).trans (by decide : 1 ≤ 3)⟩
      | later Lead f Rest hbefore hout =>
          obtain ⟨q, hq, hout⟩ := hout
          let Prefix := Lead.append (.cons f (.nil _))
          have heq : Prefix.append (Rest.append (.cons e Tail)) =
              (Lead.append (.cons f Rest)).append (.cons e Tail) := by
            simp only [Prefix, Path.append_assoc, Path.append]
          obtain ⟨T, hT⟩ := overlap_shortcut Prefix Rest (.cons e Tail) A hA S p q
            (rho p) (rho q) D (by rwa [heq]) (by rwa [heq]) hh hout F
            (hblocks p hp) (hblocks q hq)
          refine Or.inl ⟨T.weaken (by rw [heq]), ?_⟩
          simpa only [Route.hops_weaken] using hT.trans (by decide : 2 ≤ 3)
      | absent Pre _ =>
          let close := prefixRoute Pre A hA S hPreS p (rho p) D hPreShort hh F (hblocks p hp)
          let edge := Route.edge _ _ e.micro ((hF _ _).trans_eq e.weight)
          let left := close.append edge
          have hc : close.hops ≤ 1 := prefixRoute_hops _ _ _ _ _ _ _ _ _ _ _ _
          have hl : left.hops ≤ 2 := by
            have h := close.hops_append edge
            have he : edge.hops = 1 := rfl
            dsimp only [left]
            omega
          have hsubTail : Tail.edges.Sublist (Pre.append (.cons e Tail)).edges :=
            (List.sublist_cons_self _ _).trans (Pre.edges_sublist_right (.cons e Tail))
          have hbudget : Pre.micro + e.micro + Tail.micro ≤ (Pre.append (.cons e Tail)).micro := by
            simp only [Path.micro_append, Path.micro]
            omega
          exact peel_no_in_tail (Pre.append (.cons e Tail)) A hA S P rho D F hF hblocks
            Tail hTailS hTailShort hTail hsubTail (Pre.micro + e.micro) left hl hbudget

theorem final_level_shortcut (Q : Path R G s t) (A : ℕ) (hA : 0 < A)
    (S : Finset (Fin n)) (hS : Q.Inside S) (rho : Fin n → ℝ) (D : ℝ)
    (hshort : (Q.searchWeight A : ℝ) ≤ D) (hrho : ∀ p ∈ S, 0 ≤ rho p)
    (F : Graph (Fin n))
    (hblocks : ∀ p ∈ S, ∀ u v, F u v ≤
      closure (R.base G) (block (rounded A (R.restricted G S)) S p (rho p) D) u v) :
    ∃ P : Route F s t Q.micro, P.hops ≤ 1 := by
  have hs : s ∈ S := hS s Q.endpoints_support.1
  have hhit := within_self (rounded A (R.restricted G S)) s (hrho s hs)
  exact ⟨suffixRoute Q A hA S hS s (rho s) D hshort hhit F (hblocks s hs),
    suffixRoute_hops _ _ _ _ _ _ _ _ _ _ _ _⟩

end

end StreamingReachability.Late
