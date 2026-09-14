# Lax formalization workflow

Before doing any work in this repository, read `CURRENT_STATE.md` and
`WORKFLOW.md`. Treat these as the durable handoff between sessions. Consult
`SESSION_HISTORY.md` only for relevant historical decisions; the old
`FORMALIZATION_STATE.md` is a compatibility pointer.

Follow the current output of `lax print instructions` and the rules in
`lax print spec`. In particular:

- Keep mathematical concepts separate from their proofs.
- Finish and validate the concept files first, then stop for the user's review
  before beginning proof work unless the user has already authorized both
  phases.
- Do not run `lax register`; registration is permanent and belongs to the
  user.
- Record decisions, commands run, validation results, blockers, and the exact
  next action in `CURRENT_STATE.md` before ending a work session. Append
  detailed historical notes to `SESSION_HISTORY.md`, not the current summary.
