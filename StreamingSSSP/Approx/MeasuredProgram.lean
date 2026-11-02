module

public import StreamingSSSP.Approx.Augmented
public import StreamingSSSP.Hopset.ConstructionResources

@[expose] public section

namespace StreamingSSSP.Approx.Measured

open scoped Classical
open Hopset

variable {n : ℕ} {A B E : Type*}

def metadata (out : Hopset.Measured.Report n A) : Hopset.Measured.Report n A :=
  { out with passes := out.passes + 1 }

theorem auxiliary_erasure (view : E → Option (StoredEdges.Edge n)) (input : List E)
    (auxiliary : List (StoredEdges.Edge n)) :
    Hopset.Measured.eraseHandler (Hopset.Measured.auxiliaryHandler view input auxiliary) =
      Backend.guardedAuxiliaryHandler view input auxiliary := by
  rw [Hopset.Measured.auxiliaryHandler_erases, Backend.guardedAuxiliaryHandler_eq]

noncomputable def evaluate (view : E → Option (StoredEdges.Edge n)) (input : List E)
    (auxiliary : List (StoredEdges.Edge n)) : Program n A → Law (Hopset.Measured.Report n A)
  | .pure value => Law.pure ⟨value, 0, [], []⟩
  | .metadata next => (evaluate view input auxiliary (next (scanAuxiliary view input auxiliary))).map metadata
  | .construct unit builder next =>
      (Hopset.Measured.builder
        (Hopset.Measured.auxiliaryHandler (microViewed unit view) input (auxiliary.map (microMap unit))) builder).bind
          (fun first => (evaluate view input auxiliary (next first.result)).map first.then)
  | .query unit request allowance next =>
      let first := Hopset.Measured.auxiliaryHandler (microViewed unit view) input (auxiliary.map (microMap unit)) request allowance
      (evaluate view input auxiliary (next first.result)).map first.then

theorem evaluate_erases (view : E → Option (StoredEdges.Edge n)) (input : List E)
    (auxiliary : List (StoredEdges.Edge n)) (program : Program n A) (f : A → ℝ) :
    (evaluate view input auxiliary program).expect (fun out => f out.result) =
      (Program.evaluateAuxiliary view input auxiliary program).expect f := by
  induction program with
  | pure value => rfl
  | metadata next ih =>
      simp only [evaluate, Program.evaluateAuxiliary, Law.expect_map, metadata]
      exact ih _
  | construct unit builder next ih =>
      simp only [evaluate, Program.evaluateAuxiliary, Law.expect_bind, Law.expect_map, Hopset.Measured.Report.then]
      calc
        _ = (Hopset.Measured.builder (Hopset.Measured.auxiliaryHandler (microViewed unit view) input
            (auxiliary.map (microMap unit))) builder).expect
              (fun first => (Program.evaluateAuxiliary view input auxiliary (next first.result)).expect f) := by
                apply congrArg (Hopset.Measured.builder (Hopset.Measured.auxiliaryHandler (microViewed unit view) input
                  (auxiliary.map (microMap unit))) builder).expect
                funext first
                exact ih first.result
        _ = _ := by
          have h := Hopset.Measured.builder_erases
            (Hopset.Measured.auxiliaryHandler (microViewed unit view) input (auxiliary.map (microMap unit))) builder
            (fun result => (Program.evaluateAuxiliary view input auxiliary (next result)).expect f)
          rw [auxiliary_erasure] at h
          exact h
  | query unit request allowance next ih =>
      simp only [evaluate, Program.evaluateAuxiliary, Law.expect_map, Hopset.Measured.Report.then]
      rw [← auxiliary_erasure, Hopset.Measured.eraseHandler, Law.expect_bind, Law.expect_pure]
      exact ih _

theorem evaluate_expect_bind (view : E → Option (StoredEdges.Edge n)) (input : List E)
    (auxiliary : List (StoredEdges.Edge n)) (program : Program n A) (next : A → Program n B)
    (f : Hopset.Measured.Report n B → ℝ) :
    (evaluate view input auxiliary (program.bind next)).expect f =
      (evaluate view input auxiliary program).expect (fun first =>
        (evaluate view input auxiliary (next first.result)).expect (fun last => f (first.then last))) := by
  induction program generalizing f with
  | pure value =>
      simp only [Program.bind, evaluate, Law.expect_pure, Hopset.Measured.Report.then, zero_add, List.nil_append]
  | metadata resume ih =>
      simp only [Program.bind, evaluate, Law.expect_map]
      rw [ih _]
      apply congrArg (evaluate view input auxiliary (resume (scanAuxiliary view input auxiliary))).expect
      funext first
      apply congrArg (evaluate view input auxiliary (next first.result)).expect
      funext last
      congr 1
      cases first
      cases last
      simp only [metadata, Hopset.Measured.Report.then, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
  | construct unit builder resume ih =>
      simp only [Program.bind, evaluate, Law.expect_bind, Law.expect_map]
      apply congrArg (Hopset.Measured.builder (Hopset.Measured.auxiliaryHandler (microViewed unit view) input
        (auxiliary.map (microMap unit))) builder).expect
      funext first
      rw [ih first.result]
      apply congrArg (evaluate view input auxiliary (resume first.result)).expect
      funext middle
      apply congrArg (evaluate view input auxiliary (next middle.result)).expect
      funext last
      congr 1
      cases first
      cases middle
      cases last
      simp only [Hopset.Measured.Report.then, Nat.add_assoc, List.append_assoc]
  | query unit request allowance resume ih =>
      simp only [Program.bind, evaluate, Law.expect_map]
      rw [ih _]
      apply congrArg (evaluate view input auxiliary _).expect
      funext first
      apply congrArg (evaluate view input auxiliary (next first.result)).expect
      funext last
      congr 1
      cases first
      cases last
      simp only [Hopset.Measured.Report.then, Nat.add_assoc, List.append_assoc]

end StreamingSSSP.Approx.Measured
