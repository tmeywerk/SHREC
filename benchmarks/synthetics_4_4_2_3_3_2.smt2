(set-logic QF_LRA)
(declare-fun r2 () Real)
(declare-fun r0 () Real)
(declare-fun r3 () Real)
(declare-fun r1 () Real)
(assert (let ((.def_0 (* (- (/ 4484798038473809 9007199254740992)) r3))) (let ((.def_1 (* (- (/ 5884356692599299 9007199254740992)) r2))) (let ((.def_2 (* (/ 151673763425193 70368744177664) r1))) (let ((.def_3 (* (/ 4468205634830085 4503599627370496) r0))) (let ((.def_4 (+ .def_3 .def_2 .def_1 .def_0))) (let ((.def_5 (<= .def_4 (/ 5503197752880969 4503599627370496)))) (let ((.def_6 (* (/ 2931859258049389 9007199254740992) r3))) (let ((.def_7 (* (/ 474935049718641 4503599627370496) r2))) (let ((.def_8 (* (/ 2413055207140091 2251799813685248) r1))) (let ((.def_9 (* (- (/ 1480419604333179 9007199254740992)) r0))) (let ((.def_10 (+ .def_9 .def_8 .def_7 .def_6))) (let ((.def_11 (<= .def_10 (/ 2467480557615229 4503599627370496)))) (let ((.def_12 (* (/ 1937522141553571 9007199254740992) r3))) (let ((.def_13 (* (/ 291561319743355 9007199254740992) r2))) (let ((.def_14 (* (/ 582011170922263 281474976710656) r1))) (let ((.def_15 (* (- (/ 1833972395263791 4503599627370496)) r0))) (let ((.def_16 (+ .def_15 .def_14 .def_13 .def_12))) (let ((.def_17 (<= .def_16 (/ 560281154601847 2251799813685248)))) (let ((.def_18 (or .def_17 .def_11 .def_5))) (let ((.def_19 (* (/ 2844021725547751 2251799813685248) r3))) (let ((.def_20 (* (- (/ 4957516867993893 9007199254740992)) r2))) (let ((.def_21 (* (/ 3299599372398265 2251799813685248) r1))) (let ((.def_22 (* (- (/ 262248288051129 140737488355328)) r0))) (let ((.def_23 (+ .def_22 .def_21 .def_20 .def_19))) (let ((.def_24 (<= .def_23 (/ 1207409282090031 4503599627370496)))) (let ((.def_25 (* (- (/ 18550175591965 70368744177664)) r3))) (let ((.def_26 (* (/ 1850441618914125 2251799813685248) r2))) (let ((.def_27 (* (/ 5872543920468281 9007199254740992) r1))) (let ((.def_28 (* (- (/ 2497003510248055 1125899906842624)) r0))) (let ((.def_29 (+ .def_28 .def_27 .def_26 .def_25))) (let ((.def_30 (<= .def_29 (- (/ 7312106446956411 9007199254740992))))) (let ((.def_31 (* (- (/ 3364578231855129 2251799813685248)) r3))) (let ((.def_32 (* (/ 8771487264071145 9007199254740992) r2))) (let ((.def_33 (* (- (/ 493195772273693 1125899906842624)) r1))) (let ((.def_34 (* (/ 468719431672897 4503599627370496) r0))) (let ((.def_35 (+ .def_34 .def_33 .def_32 .def_31))) (let ((.def_36 (<= .def_35 (- (/ 7270086369126667 9007199254740992))))) (let ((.def_37 (or .def_36 .def_30 .def_24))) (let ((.def_38 (and .def_37 .def_18))) .def_38))))))))))))))))))))))))))))))))))))))))
(check-sat)