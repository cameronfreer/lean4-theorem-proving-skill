-- Transitive hop: B imports Middle imports A, so a stale A must be caught
-- through the dependency closure, not only as a direct import.
import Gate.A
