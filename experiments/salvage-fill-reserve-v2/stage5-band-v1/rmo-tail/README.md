# Wave D narrow-import tail

This is the separately identified 24-cell `rmo_2000_6` tail: six fixed
seeds by the four Wave D arms. It uses source
`853884ebecf0f33e0af5b96c23d797a36bfa7121` and the same resource settings
as the main Wave D matrix.

The source differs from the main Wave D runtime SHA only in runtime
narrow-import handling. Tests assert byte-identical behavior for challenges
whose pristine block is exactly `import Mathlib`.

The tail waits until every main Wave D cell has been dispatched. It never
interrupts or replaces a running paid cell, and every task has a fresh ID and
result namespace.
