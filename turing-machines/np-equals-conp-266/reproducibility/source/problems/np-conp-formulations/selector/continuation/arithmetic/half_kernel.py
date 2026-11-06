"""Half a finite natural with two consuming tests and no per-pair clear."""
from TMBuilder import subroutine


class PairHalfMixin:
    @subroutine
    def half_kernel(self):
        A, B, Q, R, C = self.micro
        return [self.label('half_pairs', [
            A.decnz, [[A.decnz, [Q.inc, 'continue_half_pairs']], R.inc]])]
