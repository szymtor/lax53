# Lax formalization workflow

Before doing any work in this repository, read `FORMALIZATION_STATE.md` in
full. Treat it as the durable handoff between sessions.

Follow the current output of `lax print instructions` and the rules in
`lax print spec`. In particular:

- Keep mathematical concepts separate from their proofs.
- Finish and validate the concept files first, then stop for the user's review
  before beginning proof work.
- Do not run `lax register`; registration is permanent and belongs to the
  user.
- Record decisions, commands run, validation results, blockers, and the exact
  next action in `FORMALIZATION_STATE.md` before ending a work session.

