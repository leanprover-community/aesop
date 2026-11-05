import Aesop.Nanos

open Aesop

#guard Nanos.printAsMillis 0 == "0.0ms"
#guard Nanos.printAsMillis 99999 == "0.0ms"
#guard Nanos.printAsMillis 100000 == "0.1ms"
#guard Nanos.printAsMillis 999999 == "0.9ms"
#guard Nanos.printAsMillis 1000000 == "1.0ms"
#guard Nanos.printAsMillis 123456789 == "123.4ms"
-- Avoid both floating-point rounding across a tenth and scientific notation.
#guard Nanos.printAsMillis 1999999 == "1.9ms"
#guard Nanos.printAsMillis 99999999999999999999 == "99999999999999.9ms"
