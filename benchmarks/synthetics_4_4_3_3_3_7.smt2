(set-logic QF_LRA)
(declare-fun r2 () Real)
(declare-fun r0 () Real)
(declare-fun r3 () Real)
(declare-fun r1 () Real)
(assert (let ((.def_0 (* (/ 7409189680948541 9007199254740992) r3))) (let ((.def_1 (* (- (/ 5237319120203391 4503599627370496)) r2))) (let ((.def_2 (* (- (/ 628421122011547 9007199254740992)) r1))) (let ((.def_3 (* (- (/ 8112330056875957 9007199254740992)) r0))) (let ((.def_4 (+ .def_3 .def_2 .def_1 .def_0))) (let ((.def_5 (<= .def_4 (- (/ 4176761096725303 9007199254740992))))) (let ((.def_6 (* (/ 4623855756109511 2251799813685248) r3))) (let ((.def_7 (* (- (/ 6499420489405239 4503599627370496)) r2))) (let ((.def_8 (* (/ 1169244996381069 562949953421312) r1))) (let ((.def_9 (* (- (/ 1363354983303985 1125899906842624)) r0))) (let ((.def_10 (+ .def_9 .def_8 .def_7 .def_6))) (let ((.def_11 (<= .def_10 (/ 368008370591245 2251799813685248)))) (let ((.def_12 (* (- (/ 743829867582609 1125899906842624)) r3))) (let ((.def_13 (* (- (/ 186445451948053 140737488355328)) r2))) (let ((.def_14 (* (/ 4864867791608167 4503599627370496) r1))) (let ((.def_15 (* (/ 3039770978381803 2251799813685248) r0))) (let ((.def_16 (+ .def_15 .def_14 .def_13 .def_12))) (let ((.def_17 (<= .def_16 (- (/ 1140566844075255 4503599627370496))))) (let ((.def_18 (or .def_17 .def_11 .def_5))) (let ((.def_19 (* (/ 2612525345227095 4503599627370496) r3))) (let ((.def_20 (* (- (/ 1683135043988549 2251799813685248)) r2))) (let ((.def_21 (* (- (/ 4980444305747835 9007199254740992)) r1))) (let ((.def_22 (* (- (/ 2439397508621887 2251799813685248)) r0))) (let ((.def_23 (+ .def_22 .def_21 .def_20 .def_19))) (let ((.def_24 (<= .def_23 (- (/ 2228458019957513 2251799813685248))))) (let ((.def_25 (* (- (/ 5639239665702549 2251799813685248)) r3))) (let ((.def_26 (* (/ 251674187792479 281474976710656) r2))) (let ((.def_27 (* (/ 1963855904537117 1125899906842624) r1))) (let ((.def_28 (* (- (/ 586331620417239 1125899906842624)) r0))) (let ((.def_29 (+ .def_28 .def_27 .def_26 .def_25))) (let ((.def_30 (<= .def_29 (- (/ 450803425638731 1125899906842624))))) (let ((.def_31 (* (- (/ 5285523604145153 9007199254740992)) r3))) (let ((.def_32 (* (/ 4106295477703963 4503599627370496) r2))) (let ((.def_33 (* (- (/ 6386730772586187 9007199254740992)) r1))) (let ((.def_34 (* (- (/ 1639350531154247 4503599627370496)) r0))) (let ((.def_35 (+ .def_34 .def_33 .def_32 .def_31))) (let ((.def_36 (<= .def_35 (- (/ 1155377957808267 2251799813685248))))) (let ((.def_37 (or .def_36 .def_30 .def_24))) (let ((.def_38 (* (/ 4983835282454507 9007199254740992) r3))) (let ((.def_39 (* (- (/ 3783685483506961 4503599627370496)) r2))) (let ((.def_40 (* (/ 121037655210575 281474976710656) r1))) (let ((.def_41 (* (/ 192178402064597 1125899906842624) r0))) (let ((.def_42 (+ .def_41 .def_40 .def_39 .def_38))) (let ((.def_43 (<= .def_42 (/ 1771900168483585 9007199254740992)))) (let ((.def_44 (* (/ 7287279628013723 9007199254740992) r3))) (let ((.def_45 (* (/ 2311283779998021 1125899906842624) r2))) (let ((.def_46 (* (/ 7493126703591049 4503599627370496) r1))) (let ((.def_47 (* (- (/ 8497630991742145 4503599627370496)) r0))) (let ((.def_48 (+ .def_47 .def_46 .def_45 .def_44))) (let ((.def_49 (<= .def_48 (/ 6739800733396113 9007199254740992)))) (let ((.def_50 (* (- (/ 1279001193539599 2251799813685248)) r3))) (let ((.def_51 (* (- (/ 2974223626946657 4503599627370496)) r2))) (let ((.def_52 (* (- (/ 7046632324952665 9007199254740992)) r1))) (let ((.def_53 (* (/ 2001575361822555 1125899906842624) r0))) (let ((.def_54 (+ .def_53 .def_52 .def_51 .def_50))) (let ((.def_55 (<= .def_54 (- (/ 1210722259580241 2251799813685248))))) (let ((.def_56 (or .def_55 .def_49 .def_43))) (let ((.def_57 (and .def_56 .def_37 .def_18))) .def_57)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
(check-sat)
