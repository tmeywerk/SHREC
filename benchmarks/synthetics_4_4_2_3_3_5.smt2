(set-logic QF_LRA)
(declare-fun r2 () Real)
(declare-fun r0 () Real)
(declare-fun r3 () Real)
(declare-fun r1 () Real)
(assert (let ((.def_0 (* (- (/ 5804986410482407 9007199254740992)) r3))) (let ((.def_1 (* (/ 6144362510615467 2251799813685248) r2))) (let ((.def_2 (* (- (/ 2509779394724713 4503599627370496)) r1))) (let ((.def_3 (* (/ 3627985570291727 2251799813685248) r0))) (let ((.def_4 (+ .def_3 .def_2 .def_1 .def_0))) (let ((.def_5 (<= .def_4 (/ 3254404022014389 2251799813685248)))) (let ((.def_6 (* (- (/ 7803372228824969 9007199254740992)) r3))) (let ((.def_7 (* (- (/ 6188685658914633 4503599627370496)) r2))) (let ((.def_8 (* (/ 1974715127316009 1125899906842624) r1))) (let ((.def_9 (* (/ 3144769187275303 1125899906842624) r0))) (let ((.def_10 (+ .def_9 .def_8 .def_7 .def_6))) (let ((.def_11 (<= .def_10 (/ 2871563131630261 2251799813685248)))) (let ((.def_12 (* (/ 2048409199099055 9007199254740992) r3))) (let ((.def_13 (* (- (/ 2316133676640583 2251799813685248)) r2))) (let ((.def_14 (* (- (/ 6747551326027675 9007199254740992)) r1))) (let ((.def_15 (* (/ 8085530917658795 4503599627370496) r0))) (let ((.def_16 (+ .def_15 .def_14 .def_13 .def_12))) (let ((.def_17 (<= .def_16 (- (/ 3440636605399979 9007199254740992))))) (let ((.def_18 (or .def_17 .def_11 .def_5))) (let ((.def_19 (* (/ 1316688654535411 2251799813685248) r3))) (let ((.def_20 (* (/ 3128339059770485 4503599627370496) r2))) (let ((.def_21 (* (- (/ 1192219460721487 1125899906842624)) r1))) (let ((.def_22 (* (- (/ 971153036304057 562949953421312)) r0))) (let ((.def_23 (+ .def_22 .def_21 .def_20 .def_19))) (let ((.def_24 (<= .def_23 (- (/ 2475405057393829 4503599627370496))))) (let ((.def_25 (* (- (/ 241949108411863 281474976710656)) r3))) (let ((.def_26 (* (/ 781190506311357 1125899906842624) r2))) (let ((.def_27 (* (- (/ 2078064293735419 562949953421312)) r1))) (let ((.def_28 (* (/ 6605953186728663 4503599627370496) r0))) (let ((.def_29 (+ .def_28 .def_27 .def_26 .def_25))) (let ((.def_30 (<= .def_29 (- (/ 718396186856265 562949953421312))))) (let ((.def_31 (* (/ 5868063290999913 9007199254740992) r3))) (let ((.def_32 (* (/ 8526898061025899 9007199254740992) r2))) (let ((.def_33 (* (- (/ 3008391036192611 2251799813685248)) r1))) (let ((.def_34 (* (- (/ 2061358567243783 9007199254740992)) r0))) (let ((.def_35 (+ .def_34 .def_33 .def_32 .def_31))) (let ((.def_36 (<= .def_35 (- (/ 1483046615176919 4503599627370496))))) (let ((.def_37 (or .def_36 .def_30 .def_24))) (let ((.def_38 (and .def_37 .def_18))) .def_38))))))))))))))))))))))))))))))))))))))))
(check-sat)
