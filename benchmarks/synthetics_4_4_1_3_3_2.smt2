(set-logic QF_LRA)
(declare-fun r2 () Real)
(declare-fun r0 () Real)
(declare-fun r3 () Real)
(declare-fun r1 () Real)
(assert (let ((.def_0 (* (- (/ 1000706239943277 9007199254740992)) r3))) (let ((.def_1 (* (/ 1949958203702335 9007199254740992) r2))) (let ((.def_2 (* (/ 5904899239978765 2251799813685248) r1))) (let ((.def_3 (* (/ 3761339126357981 9007199254740992) r0))) (let ((.def_4 (+ .def_3 .def_2 .def_1 .def_0))) (let ((.def_5 (<= .def_4 (/ 2355992033208463 2251799813685248)))) (let ((.def_6 (* (- (/ 3134740178073099 9007199254740992)) r3))) (let ((.def_7 (* (/ 1188076423864367 4503599627370496) r2))) (let ((.def_8 (* (/ 1685872236357 8796093022208) r1))) (let ((.def_9 (* (/ 1852513798128511 4503599627370496) r0))) (let ((.def_10 (+ .def_9 .def_8 .def_7 .def_6))) (let ((.def_11 (<= .def_10 (/ 143318410473647 2251799813685248)))) (let ((.def_12 (* (/ 1514645670686691 2251799813685248) r3))) (let ((.def_13 (* (- (/ 3438420073680081 9007199254740992)) r2))) (let ((.def_14 (* (- (/ 473039804701957 4503599627370496)) r1))) (let ((.def_15 (* (/ 225051093434073 4503599627370496) r0))) (let ((.def_16 (+ .def_15 .def_14 .def_13 .def_12))) (let ((.def_17 (<= .def_16 (- (/ 968407651414619 9007199254740992))))) (let ((.def_18 (or .def_17 .def_11 .def_5))) .def_18))))))))))))))))))))
(check-sat)
