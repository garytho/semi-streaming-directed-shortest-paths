module

public import StreamingSSSP.Hopset.ShortTreeCounts
public import StreamingSSSP.Hopset.ReplayCounters

@[expose] public section

namespace StreamingSSSP.Hopset.Following

open scoped Classical
open Batched

noncomputable section

variable {n : ℕ} {cfg : Config} {stored : Implicit.Representation n}
    {input : List (StoredEdges.Edge n)} {rank : Vector ℕ n}

theorem familyCount_observed (hnum : 0 < cfg.initialNumerator)
    (hEarly : cfg.earlyLevel ≤ cfg.maximumLevel) {fuel q : ℕ} {queue : List (Finset (Fin n))}
    (run : FullExecution cfg stored input rank fuel q queue)
    (hlevel : q + fuel = cfg.maximumLevel + 1) (hq : q ≤ cfg.earlyLevel)
    (hg : TraceGood cfg stored input run.entries)
    (known : Fin n → Option (Fin q))
    (paths : List (TrackedPath stored input queue.toArray.toVector)) (layers : List (Layer cfg stored input))
    (final : State cfg stored input cfg.earlyLevel)
    (hf : followControls cfg hnum stored input (fun v => rank.get v) (run.entries.map GeometricEntry.control)
      (some ⟨q, ⟨known, queue, paths, layers⟩⟩) = some ⟨cfg.earlyLevel, final⟩)
    (d : ℕ) (hd : q + d ≤ cfg.earlyLevel) :
    familyCount hnum run paths d ≤ observedCount hnum (q + d) (some final) := by
  induction run generalizing layers d with
  | done =>
      have hbad : cfg.maximumLevel + 1 ≤ cfg.maximumLevel := by omega
      omega
  | @next fuel q queue frame valid rest ih =>
      let st : State cfg stored input q := ⟨known, queue, paths, layers⟩
      by_cases he : q < cfg.earlyLevel
      · let coins := fun v => decide (rank.get v = q)
        let makeState := fun choices : Fin queue.toArray.size → Reference.Choice n cfg =>
          { known := fun v => RankPrefix.nextKnown q (known v) (coins v)
            queue := geometricChildren cfg q stored input queue.toArray.toVector choices
            paths := advanceAll cfg q hnum he choices (splitAll cfg q hnum paths) (splitAll_short cfg q hnum paths)
            layers := layers ++ [⟨q, queue, paths, choices⟩] : State cfg stored input (q + 1) }
        let next := makeState frame.choices
        have hupdate : st.update hnum he (coins, fun i => (frame.choices i).owners) = next :=
          congrArg makeState (valid.currentChoices he)
        have hfollow : followControls cfg hnum stored input (fun v => rank.get v)
            (rest.entries.map GeometricEntry.control) (some ⟨q + 1, next⟩) = some ⟨cfg.earlyLevel, final⟩ := by
          rw [← hupdate]
          exact (follow_valid_head hnum st frame valid he _).symm.trans hf
        cases d with
        | zero =>
            have hm := follow_recorded_le hnum (fun v => rank.get v) (rest.entries.map GeometricEntry.control)
              (q + 1) next ⟨cfg.earlyLevel, final⟩ hfollow q
            have hrec : recordedCount hnum q next.layers =
                recordedCount hnum q layers + (splitAll cfg q hnum paths).length := by
              have h := recordedCount_update hnum he st (coins, fun i => (frame.choices i).owners) q
              rw [hupdate] at h
              simpa only [st, ↓reduceIte] using h
            rw [familyCount_zero]
            simp only [Nat.add_zero, observedCount, he, ↓reduceIte]
            exact (show (splitAll cfg q hnum paths).length ≤ recordedCount hnum q next.layers by
              rw [hrec]; omega).trans hm
        | succ d =>
            have hc : familyCount hnum (.next frame valid rest) paths (d + 1) =
                familyCount hnum rest next.paths d :=
              familyCount_step hnum he frame valid rest paths d
            have ht := ih (by omega) (by omega) (FullExecution.tail_good hg)
              next.known next.paths next.layers hfollow d (by omega)
            have heq : q + 1 + d = q + (d + 1) := by omega
            exact hc.trans_le (by simpa only [heq] using ht)
      · have heq : q = cfg.earlyLevel := by omega
        have hd0 : d = 0 := by omega
        subst q d
        have hs : st = final := by
          have h := congrArg (unpackState cfg.earlyLevel) hf
          rw [followControls_done cfg hnum stored input (fun v => rank.get v)
            ((FullExecution.next frame valid rest).entries.map GeometricEntry.control) cfg.earlyLevel st le_rfl] at h
          simpa only [unpackState, ↓reduceDIte, Option.some.injEq] using h
        subst final
        have hgood : AllGood cfg stored input cfg.earlyLevel queue := hg _ List.mem_cons_self
        rw [familyCount_zero]
        simp only [Nat.add_zero, observedCount, lt_self_iff_false, ↓reduceIte, State.primeCount, st, hgood, le_refl]

end

end StreamingSSSP.Hopset.Following
