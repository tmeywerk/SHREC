(set-logic QF_LRA)
(declare-fun r2 () Real)
(declare-fun r0 () Real)
(declare-fun r3 () Real)
(declare-fun r1 () Real)
(assert (let ((.def_0 (* (- (/ 4644143759431275 9007199254740992)) r3))) (let ((.def_1 (* (- (/ 307552871656799 281474976710656)) r2))) (let ((.def_2 (* (/ 3298413907398861 4503599627370496) r1))) (let ((.def_3 (* (- (/ 3700299863788277 4503599627370496)) r0))) (let ((.def_4 (+ .def_3 .def_2 .def_1 .def_0))) (let ((.def_5 (<= .def_4 (- (/ 8848912954461549 9007199254740992))))) (let ((.def_6 (* (- (/ 642517089889147 4503599627370496)) r3))) (let ((.def_7 (* (/ 332900410027159 2251799813685248) r2))) (let ((.def_8 (* (- (/ 1501397335872217 2251799813685248)) r1))) (let ((.def_9 (* (/ 415681900598759 140737488355328) r0))) (let ((.def_10 (+ .def_9 .def_8 .def_7 .def_6))) (let ((.def_11 (<= .def_10 (/ 1875925091448427 9007199254740992)))) (let ((.def_12 (* (/ 322862525723961 281474976710656) r3))) (let ((.def_13 (* (- (/ 1444804928671197 1125899906842624)) r2))) (let ((.def_14 (* (/ 4721596864349945 2251799813685248) r1))) (let ((.def_15 (* (- (/ 956357738000449 1125899906842624)) r0))) (let ((.def_16 (+ .def_15 .def_14 .def_13 .def_12))) (let ((.def_17 (<= .def_16 (- (/ 2355129664502117 9007199254740992))))) (let ((.def_18 (or .def_17 .def_11 .def_5))) (let ((.def_19 (* (- (/ 2919144856534411 9007199254740992)) r3))) (let ((.def_20 (* (- (/ 2787588519008273 4503599627370496)) r2))) (let ((.def_21 (* (- (/ 3479946973270175 4503599627370496)) r1))) (let ((.def_22 (* (/ 3807292810248957 4503599627370496) r0))) (let ((.def_23 (+ .def_22 .def_21 .def_20 .def_19))) (let ((.def_24 (<= .def_23 (- (/ 5333128476095097 9007199254740992))))) (let ((.def_25 (* (- (/ 6319724899602335 9007199254740992)) r3))) (let ((.def_26 (* (- (/ 2938263348343929 2251799813685248)) r2))) (let ((.def_27 (* (/ 8272916417594311 2251799813685248) r1))) (let ((.def_28 (* (/ 3715454053486719 2251799813685248) r0))) (let ((.def_29 (+ .def_28 .def_27 .def_26 .def_25))) (let ((.def_30 (<= .def_29 (/ 2402159314208869 2251799813685248)))) (let ((.def_31 (* (/ 359664036023475 2251799813685248) r3))) (let ((.def_32 (* (/ 151864483243313 281474976710656) r2))) (let ((.def_33 (* (/ 598758761238151 1125899906842624) r1))) (let ((.def_34 (* (- (/ 2989010937294681 4503599627370496)) r0))) (let ((.def_35 (+ .def_34 .def_33 .def_32 .def_31))) (let ((.def_36 (<= .def_35 (/ 339675488856267 4503599627370496)))) (let ((.def_37 (or .def_36 .def_30 .def_24))) (let ((.def_38 (and .def_37 .def_18))) .def_38))))))))))))))))))))))))))))))))))))))))
(check-sat)