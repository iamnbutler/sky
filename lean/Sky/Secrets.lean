module

public import Sky.Proofs

/-! # Where the secrets go

* **The password** (`PasswordSent`). Every step but Sign In has the same effects whatever the
  password field holds (`step_blind_effects`). Sign In's effects are the same too once the one
  redacted request is blanked (`scrub`), for any password that shows the same (Cairn's
  `SecureField.Agree`: as many bullets); and with Sign In enabled its only request is
  `createSession` with the password, marked `redact`, and the field is empty after
  (`signIn_requests`). So the password reaches one request, once per typing.
* **Signing out** (`SignOutForgets`, `SignedOutNoSecret`). Sign Out's effects include a
  `forgetSecret` of both Keychain items; while signed out, no step sends a request carrying a
  Keychain secret. -/

@[expose] public section

namespace Sky
open Cairn CairnAtproto CairnAtproto.Session

/-! ## The password -/

/-- A request with its redacted contents blanked: what tools may show of it. -/
def scrubReq : Request → Request
  | .http _ _ _ _ _ _ _ true => .http "" "" [] ByteArray.empty 0 none [] true
  | r => r

def scrubEffect : Effect → Effect
  | .request id r => .request id (scrubReq r)
  | e => e

def scrub (es : List Effect) : List Effect := es.map scrubEffect

def reqOf : Effect → Option Request
  | .request _ r => some r
  | _ => none

theorem createSession_redact (host i p : String) : (createSession host i p).redact = true := rfl

theorem scrub_createSession (host i p q : String) :
    scrubReq (createSession host i p) = scrubReq (createSession host i q) := rfl

theorem secure_apply_snd (op : TextOp) (f g : Text.SecureField) :
    (Text.SecureField.apply op f).2 = (Text.SecureField.apply op g).2 := by
  cases op <;> rfl

theorem settle_snd (s : State) :
    (settle s).2 = if live s.session then []
      else cancelEffects (Session.step s.session (.cancel (pids s.session))).2 := by
  unfold settle; split <;> rfl

theorem step_blind_effects (s : State) (c : Cmd) (p : Text.SecureField) (hc : c ≠ .signIn) :
    (s.step c).2 = ({ s with password := p }.step c).2 := by
  cases c with
  | signIn => exact absurd rfl hc
  | editPassword op =>
    show (Text.SecureField.apply op s.password).2 ++ (settle _).2 =
      (Text.SecureField.apply op p).2 ++ (settle _).2
    rw [secure_apply_snd op s.password p, settle_snd, settle_snd]
  | _ => rfl

theorem cancelEffects_reqs (outs : List Out) : (cancelEffects outs).filterMap reqOf = [] := by
  rw [List.filterMap_eq_nil_iff]
  intro e he
  simp only [cancelEffects, List.mem_filterMap] at he
  obtain ⟨o, -, ho⟩ := he
  cases o <;> simp at ho
  subst ho; rfl

theorem settle_reqs (s : State) : (settle s).2.filterMap reqOf = [] := by
  rw [settle_snd]; split
  · rfl
  · exact cancelEffects_reqs _

/-- Sign In, enabled: the step it is. -/
theorem signIn_run {s : State} (h : ready s = true) :
    step1 s .signIn =
      ((settle { s with password := Text.SecureField.empty passwordHint, host := serviceOf s,
                        problem := none, accountOpen := false, slow := false,
                        session := { s.session with phase := .signingIn s.session.next (serviceOf s),
                                                    next := s.session.next + 1 } }).1,
       [.request (sessionId s.session.next)
          (createSession (serviceOf s) (identifierOf s) s.password.text),
        .setTimer slowTimer slowMs] ++
       (settle { s with password := Text.SecureField.empty passwordHint, host := serviceOf s,
                        problem := none, accountOpen := false, slow := false,
                        session := { s.session with phase := .signingIn s.session.next (serviceOf s),
                                                    next := s.session.next + 1 } }).2) := by
  have hc : canSignIn s.session = true := by simp only [ready, Bool.and_eq_true] at h; exact h.2
  simp only [step1, step0, signIn, h, ↓reduceIte, driveSession, drive, signIn_step hc]
  simp [signedInEvent, handleOuts, handleOut]

theorem ready_agree {s : State} {p : Text.SecureField} (h : s.password.Agree p) :
    ready { s with password := p } = ready s := by
  have hl := h.1
  have e : p.field.text.isEmpty = s.password.field.text.isEmpty := by
    cases h1 : p.field.text <;> cases h2 : s.password.field.text <;> simp_all
  simp only [ready, e]

/-- Sign In's effects, scrubbed, are the same for any password that shows the same. -/
theorem signIn_scrub (s : State) (p : Text.SecureField) (hp : s.password.Agree p) :
    scrub (s.step .signIn).2 = scrub ({ s with password := p }.step .signIn).2 := by
  show scrub (step1 s .signIn).2 = scrub (step1 { s with password := p } .signIn).2
  by_cases hr : ready s = true
  · have hr' : ready { s with password := p } = true := (ready_agree hp).trans hr
    rw [signIn_run hr, signIn_run hr']
    simp only [scrub, List.map_append, List.map_cons, List.map_nil, scrubEffect]
    rw [scrub_createSession _ _ s.password.text p.text]
    rfl
  · have hr' : ready { s with password := p } = false := by
      rw [ready_agree hp]; simpa using hr
    simp only [Bool.not_eq_true] at hr
    simp only [step1, step0, signIn, hr, hr', Bool.false_eq_true, ↓reduceIte]
    rw [settle_snd, settle_snd]

/-- Sign In, enabled: its only request is `createSession` with the password, and the field is
empty after. -/
theorem signIn_requests {s : State} (h : ready s = true) :
    (s.step .signIn).2.filterMap reqOf =
      [createSession (serviceOf s) (identifierOf s) s.password.text] ∧
    (s.step .signIn).1.password = Text.SecureField.empty passwordHint := by
  refine ⟨?_, (signIn_post h).1⟩
  show (step1 s .signIn).2.filterMap reqOf = _
  rw [signIn_run h, List.filterMap_append, settle_reqs]
  rfl

/-- ^26: the password reaches one request. -/
def PasswordSent : Prop :=
  (∀ (s : State) (c : Cmd) (p : Text.SecureField), c ≠ .signIn →
    (s.step c).2 = ({ s with password := p }.step c).2) ∧
  (∀ (s : State) (p : Text.SecureField), s.password.Agree p →
    scrub (s.step .signIn).2 = scrub ({ s with password := p }.step .signIn).2) ∧
  (∀ (s : State), ready s = true →
    (s.step .signIn).2.filterMap reqOf =
      [createSession (serviceOf s) (identifierOf s) s.password.text] ∧
    (s.step .signIn).1.password = Text.SecureField.empty passwordHint) ∧
  (∀ host i p, (createSession host i p).redact = true)

theorem passwordSent : PasswordSent :=
  ⟨step_blind_effects, signIn_scrub, fun _ h => signIn_requests h, createSession_redact⟩

/-! ## Signing out -/

/-- An effect that sends a Keychain secret. -/
def effSecret : Effect → Bool
  | .request _ r => (secretOf r).isSome
  | _ => false

def NoSecret (es : List Effect) : Prop := ∀ e ∈ es, effSecret e = false

theorem noSecret_nil : NoSecret [] := fun _ h => absurd h List.not_mem_nil

theorem noSecret_append {a b : List Effect} (ha : NoSecret a) (hb : NoSecret b) :
    NoSecret (a ++ b) := fun e he => (List.mem_append.1 he).elim (ha e) (hb e)

theorem cancelEffects_noSecret (outs : List Out) : NoSecret (cancelEffects outs) := by
  intro e he
  simp only [cancelEffects, List.mem_filterMap] at he
  obtain ⟨o, -, ho⟩ := he
  cases o <;> simp_all [effSecret]
  subst ho; rfl

theorem settle_noSecret (s : State) : NoSecret (settle s).2 := by
  rw [settle_snd]; split
  · exact noSecret_nil
  · exact cancelEffects_noSecret _

theorem sendOwn_noSecret (s : State) (k : Own) (r : Request) (hr : secretOf r = none) :
    NoSecret (sendOwn s k r).2 := by
  intro e he
  simp only [sendOwn, List.mem_singleton] at he
  subst he; simp [effSecret, hr]

theorem withdraw_noSecret (ss : Session.State) (l : Nat) : NoSecret (withdraw ss l).2 :=
  cancelEffects_noSecret _

theorem onAnswer_noSecret (s : State) (id : Nat) (a : Answer) : NoSecret (onAnswer s id a).2 := by
  unfold onAnswer
  generalize readPage a = pr
  obtain ⟨page, prob⟩ := pr
  dsimp only
  split
  · split
    · exact noSecret_nil
    · split
      · try dsimp only
        split
        · exact withdraw_noSecret _ _
        · exact noSecret_nil
      · exact noSecret_nil
  · split
    · exact noSecret_nil
    · exact noSecret_nil

theorem onEvent_noSecret (s : State) (e : Session.Event) : NoSecret (onEvent s e).2 := by
  cases e with
  | signedIn a => exact sendOwn_noSecret _ _ _ rfl
  | signedOut why => cases why <;> exact noSecret_nil
  | _ => exact noSecret_nil

theorem foldl_noSecret : ∀ (outs : List Out) (acc : State × List Effect),
    NoSecret acc.2 → (∀ o ∈ outs, o.hasSecret = false) →
    NoSecret (outs.foldl handleOut acc).2
  | [], _, h, _ => h
  | o :: rest, acc, h, ho => by
    simp only [List.foldl_cons]
    apply foldl_noSecret rest _ _ (fun o' h' => ho o' (List.mem_cons_of_mem _ h'))
    have h0 := ho o (List.mem_cons_self ..)
    cases o with
    | send rid k r =>
      refine noSecret_append h ?_
      intro e he
      simp only [List.mem_singleton] at he
      subst he
      simpa [effSecret, Out.hasSecret] using h0
    | forget rid item =>
      refine noSecret_append h ?_
      intro e he; simp only [List.mem_singleton] at he; subst he; rfl
    | cancel rid =>
      refine noSecret_append h ?_
      intro e he; simp only [List.mem_singleton] at he; subst he; rfl
    | answer id a => exact noSecret_append h (onAnswer_noSecret _ _ _)
    | event e => exact noSecret_append h (onEvent_noSecret _ _)

theorem drive_noSecret (s : State) (i : Session.Input)
    (h : ∀ o ∈ (Session.step s.session i).2, o.hasSecret = false) : NoSecret (drive s i).2 :=
  foldl_noSecret _ _ noSecret_nil h

theorem onCallReply_noSignedIn (ss : Session.State) (rid : Nat) (r : Cairn.Reply)
    (h : ss.phase = .signedOut) : (onCallReply ss rid r).2.any signedInEvent = false := by
  unfold onCallReply
  split
  · simp [forgetBoth, signedInEvent]
  · split
    · rfl
    · dsimp only
      split
      · split
        all_goals first | (simp [signedInEvent]; done) | (simp_all; done) | (rw [h] at *; contradiction) | (rename_i e; rw [h] at e; cases e)
      · simp [signedInEvent]

/-- Signed out, the session signs no one in within one step. -/
theorem signedOut_noSignedIn (ss : Session.State) (i : Session.Input) (h : ss.phase = .signedOut) :
    (Session.step ss i).2.any signedInEvent = false := by
  cases i with
  | signIn host id pw =>
    simp only [Session.step, h]
    split <;> simp [signedInEvent]
  | resume host => simp [Session.step, h]
  | call id c => simp [Session.step, h, signedInEvent]
  | signOut => simp [Session.step, h, forgetBoth, answerAll, signedInEvent]
  | cancel ids => simp [Session.step, signedInEvent]
  | reply rid r =>
    simp only [Session.step, h]
    exact onCallReply_noSignedIn _ _ _ h

theorem driveSession_noSecret (s : State) (i : Session.Input) (h : s.session.phase = .signedOut) :
    NoSecret (driveSession s i).2 := by
  have hn : s.session.phase.noSession = true := by rw [h]; rfl
  have hd := drive_noSecret s i (step_noSecret _ i hn)
  simp only [driveSession, signedOut_noSignedIn _ i h, Bool.false_eq_true, ↓reduceIte]
  exact hd

theorem field_noSecret (op : TextOp) (f : Text.Field) : NoSecret (Text.Field.apply op f).2 := by
  intro e he
  cases op <;> simp only [Text.Field.apply, Text.Field.undo, Text.Field.redo,
    Text.Field.clipboard] at he <;> (repeat' split at he) <;> simp_all [effSecret]

theorem secureField_noSecret (op : TextOp) (f : Text.SecureField) :
    NoSecret (Text.SecureField.apply op f).2 := by
  cases op
  case copy | cut | undo | redo =>
    intro e he; simp [Text.SecureField.apply] at he; subst he; rfl
  all_goals exact field_noSecret _ _

theorem live_signedOut {ss : Session.State} (h : ss.phase = .signedOut) : live ss = false := by
  simp [live, h]

theorem step0_noSecret (s : State) (c : Cmd) (h : s.session.phase = .signedOut) :
    NoSecret (step0 s c).2 := by
  cases c with
  | signIn =>
    simp only [step0, signIn]
    split
    · exact noSecret_append (driveSession_noSecret _ _ h) (fun e he => by
        simp only [List.mem_singleton] at he; subst he; rfl)
    · exact noSecret_nil
  | loadMore =>
    simp only [step0, startLoadMore, canLoadMore, live_signedOut h, Bool.false_and]
    exact noSecret_nil
  | refresh =>
    simp only [step0, startRefresh_dead (live_signedOut h)]
    exact noSecret_nil
  | signOut =>
    simp only [step0, signOut]
    exact noSecret_append (driveSession_noSecret _ _ h) (sendOwn_noSecret _ _ _ rfl)
  | editIdentifier op => exact field_noSecret _ _
  | editPassword op => exact secureField_noSecret _ _
  | editService op => exact field_noSecret _ _
  | nextField => intro e he; simp only [step0, List.mem_singleton] at he; subst he; rfl
  | toggleAccount => exact noSecret_nil
  | openHelp => exact sendOwn_noSecret _ _ _ rfl
  | msg m =>
    simp only [step0]
    cases m with
    | reply id r =>
      simp only [receive0]
      split
      · next k _ =>
        cases k with
        | readService => exact sendOwn_noSecret _ _ _ rfl
        | readAccount =>
          simp only [onReadAccount]
          split
          all_goals first | exact noSecret_nil | simp_all
        | _ => exact noSecret_nil
      · split
        · exact driveSession_noSecret _ _ h
        · exact noSecret_nil
    | timer n =>
      simp only [receive0]
      split <;> exact noSecret_nil
    | _ => exact noSecret_nil

/-- While signed out, no step sends a request carrying a Keychain secret. -/
def SignedOutNoSecret : Prop :=
  ∀ (s : State) (c : Cmd), s.session.phase = .signedOut → NoSecret (s.step c).2

theorem signedOutNoSecret : SignedOutNoSecret := by
  intro s c h
  rcases step_cases s c with e | e <;> rw [e]
  · exact noSecret_append (step0_noSecret s c h) (settle_noSecret _)
  · exact noSecret_append (step0_noSecret s.blank c h) (settle_noSecret _)

/-! ## Sign Out forgets both items -/

theorem foldl_keeps : ∀ (outs : List Out) (acc : State × List Effect),
    ∃ t, (outs.foldl handleOut acc).2 = acc.2 ++ t
  | [], acc => ⟨[], by simp⟩
  | o :: rest, acc => by
    simp only [List.foldl_cons]
    obtain ⟨t, ht⟩ := foldl_keeps rest (handleOut acc o)
    rw [ht]
    cases o <;> simp [handleOut]

theorem foldl_forget : ∀ (outs : List Out) (acc : State × List Effect) (rid : Nat) (item : String),
    Out.forget rid item ∈ outs →
    Effect.request (sessionId rid) (.forgetSecret item) ∈ (outs.foldl handleOut acc).2
  | [], _, _, _, h => absurd h List.not_mem_nil
  | o :: rest, acc, rid, item, h => by
    simp only [List.foldl_cons]
    rcases List.mem_cons.1 h with e | e
    · subst e
      obtain ⟨t, ht⟩ := foldl_keeps rest (handleOut acc (.forget rid item))
      rw [ht]
      simp [handleOut]
    · exact foldl_forget rest _ rid item e

/-- Sign Out asks the host to forget both Keychain items. -/
def SignOutForgets : Prop :=
  ∀ (s : State), (∃ a, Effect.request a (.forgetSecret accessItem) ∈ (s.step .signOut).2) ∧
    (∃ b, Effect.request b (.forgetSecret refreshItem) ∈ (s.step .signOut).2)

theorem driveSession_keeps (s : State) (i : Session.Input) :
    ∃ t, (driveSession s i).2 = (drive s i).2 ++ t := by
  simp only [driveSession]
  split
  · exact ⟨_, rfl⟩
  · exact ⟨[], by simp⟩

theorem signOutForgets : SignOutForgets := by
  intro s
  let t : State := { s.blank with problem := none, accountOpen := false }
  have hf : ∀ item, item = accessItem ∨ item = refreshItem →
      ∃ a, Effect.request a (.forgetSecret item) ∈ (s.step .signOut).2 := by
    intro item hi
    have ho : Out.forget (if item = accessItem then t.session.next else t.session.next + 1) item ∈
        (Session.step t.session .signOut).2 := by
      rcases hi with rfl | rfl <;> simp [Session.step, forgetBoth, accessItem, refreshItem]
    refine ⟨sessionId (if item = accessItem then t.session.next else t.session.next + 1), ?_⟩
    show _ ∈ (step1 s.blank .signOut).2
    obtain ⟨u, hu⟩ := driveSession_keeps t .signOut
    simp only [step1, step0, signOut]
    apply List.mem_append_left
    apply List.mem_append_left
    show _ ∈ (driveSession t .signOut).2
    rw [hu]
    exact List.mem_append_left _ (foldl_forget _ _ _ _ ho)
  exact ⟨hf _ (Or.inl rfl), hf _ (Or.inr rfl)⟩

end Sky
