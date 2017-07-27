(declare-fun TurnIndicator::state0::Flash_Ctrl@0::tilOld () (_ BitVec 8))
(declare-fun TurnIndicator::state0::Flash_Ctrl@0::tilLevel () (_ BitVec 8))
(declare-fun TurnIndicator::state0::Flash_Ctrl@0::emerSwitch () Bool)
(declare-fun TurnIndicator::state0::Flash_Ctrl@0::HasOutput_output () (_ BitVec 1))
(declare-fun TurnIndicator::state0::Output_Ctrl@0::ctr () (_ BitVec 8))
(declare-fun TurnIndicator::state0::Output_Ctrl@0::lOld () Bool)
(declare-fun TurnIndicator::state0::Output_Ctrl@0::rOld () Bool)
(declare-fun TurnIndicator::state0::Output_Ctrl@0::left () Bool)
(declare-fun TurnIndicator::state0::Output_Ctrl@0::right () Bool)
(declare-fun TurnIndicator::state0::Output_Ctrl@0::lampsLeft () Bool)
(declare-fun TurnIndicator::state0::Output_Ctrl@0::lampsRight () Bool)
(declare-fun TurnIndicator::state0::Output_Ctrl@0::HasOutput_flash () (_ BitVec 1))
(declare-fun TurnIndicator::state1::Flash_Ctrl@0::tilOld () (_ BitVec 8))
(declare-fun TurnIndicator::state1::Flash_Ctrl@0::tilLevel () (_ BitVec 8))
(declare-fun TurnIndicator::state1::Flash_Ctrl@0::emerSwitch () Bool)
(declare-fun TurnIndicator::state1::Flash_Ctrl@0::HasOutput_output () (_ BitVec 1))
(declare-fun TurnIndicator::state1::Output_Ctrl@0::ctr () (_ BitVec 8))
(declare-fun TurnIndicator::state1::Output_Ctrl@0::lOld () Bool)
(declare-fun TurnIndicator::state1::Output_Ctrl@0::rOld () Bool)
(declare-fun TurnIndicator::state1::Output_Ctrl@0::left () Bool)
(declare-fun TurnIndicator::state1::Output_Ctrl@0::right () Bool)
(declare-fun TurnIndicator::state1::Output_Ctrl@0::lampsLeft () Bool)
(declare-fun TurnIndicator::state1::Output_Ctrl@0::lampsRight () Bool)
(declare-fun TurnIndicator::state1::Output_Ctrl@0::HasOutput_flash () (_ BitVec 1))
(declare-fun preconditions () Bool)
(declare-fun postconditions () Bool)
(declare-fun frameconditions () Bool)
(assert (or (= TurnIndicator::state0::Flash_Ctrl@0::HasOutput_output #b1)))
(assert (= ((_ extract 0 0) TurnIndicator::state0::Output_Ctrl@0::HasOutput_flash) ((_ extract 0 0) TurnIndicator::state0::Flash_Ctrl@0::HasOutput_output)))
(assert (or (= TurnIndicator::state0::Output_Ctrl@0::HasOutput_flash #b1)))
(assert (and (bvuge TurnIndicator::state0::Flash_Ctrl@0::tilLevel (_ bv0 8)) (bvule TurnIndicator::state0::Flash_Ctrl@0::tilLevel (_ bv2 8))))
(assert (and (bvuge TurnIndicator::state0::Flash_Ctrl@0::tilOld (_ bv0 8)) (bvule TurnIndicator::state0::Flash_Ctrl@0::tilOld (_ bv2 8))))
(assert (or (= TurnIndicator::state1::Flash_Ctrl@0::HasOutput_output #b1)))
(assert (= ((_ extract 0 0) TurnIndicator::state1::Output_Ctrl@0::HasOutput_flash) ((_ extract 0 0) TurnIndicator::state1::Flash_Ctrl@0::HasOutput_output)))
(assert (or (= TurnIndicator::state1::Output_Ctrl@0::HasOutput_flash #b1)))
(assert (and (bvuge TurnIndicator::state1::Flash_Ctrl@0::tilLevel (_ bv0 8)) (bvule TurnIndicator::state1::Flash_Ctrl@0::tilLevel (_ bv2 8))))
(assert (and (bvuge TurnIndicator::state1::Flash_Ctrl@0::tilOld (_ bv0 8)) (bvule TurnIndicator::state1::Flash_Ctrl@0::tilOld (_ bv2 8))))
(assert (= preconditions (and (or (or (= TurnIndicator::state0::Output_Ctrl@0::left true) (= TurnIndicator::state0::Output_Ctrl@0::right true)) (and (bvuge TurnIndicator::state0::Output_Ctrl@0::ctr (_ bv1 8)) (bvult TurnIndicator::state0::Output_Ctrl@0::ctr (_ bv3 8)))) (and (= TurnIndicator::state0::Output_Ctrl@0::lampsLeft false) (= TurnIndicator::state0::Output_Ctrl@0::lampsRight false)))))
(assert (= postconditions (and (=> (or (= TurnIndicator::state0::Output_Ctrl@0::left true) (= TurnIndicator::state0::Output_Ctrl@0::lOld true)) (= TurnIndicator::state1::Output_Ctrl@0::lampsLeft true)) (=> (or (= TurnIndicator::state0::Output_Ctrl@0::right true) (= TurnIndicator::state0::Output_Ctrl@0::rOld true)) (= TurnIndicator::state1::Output_Ctrl@0::lampsRight true)) (=> (bvult TurnIndicator::state0::Output_Ctrl@0::ctr (_ bv3 8)) (= TurnIndicator::state1::Output_Ctrl@0::ctr (bvadd TurnIndicator::state0::Output_Ctrl@0::ctr (_ bv1 8)))) (=> (bvuge TurnIndicator::state0::Output_Ctrl@0::ctr (_ bv3 8)) (= TurnIndicator::state1::Output_Ctrl@0::ctr TurnIndicator::state0::Output_Ctrl@0::ctr)) (= TurnIndicator::state1::Output_Ctrl@0::left TurnIndicator::state0::Output_Ctrl@0::left) (= TurnIndicator::state1::Output_Ctrl@0::right TurnIndicator::state0::Output_Ctrl@0::right) (= TurnIndicator::state1::Flash_Ctrl@0::emerSwitch TurnIndicator::state0::Flash_Ctrl@0::emerSwitch) (= TurnIndicator::state1::Flash_Ctrl@0::tilOld TurnIndicator::state0::Flash_Ctrl@0::tilOld) (= TurnIndicator::state1::Flash_Ctrl@0::tilLevel TurnIndicator::state0::Flash_Ctrl@0::tilLevel) (= TurnIndicator::state1::Output_Ctrl@0::lOld TurnIndicator::state0::Output_Ctrl@0::lOld) (= TurnIndicator::state1::Output_Ctrl@0::rOld TurnIndicator::state0::Output_Ctrl@0::rOld))))
(assert (= frameconditions (and (= TurnIndicator::state1::Flash_Ctrl@0::HasOutput_output TurnIndicator::state0::Flash_Ctrl@0::HasOutput_output) (= TurnIndicator::state1::Output_Ctrl@0::HasOutput_flash TurnIndicator::state0::Output_Ctrl@0::HasOutput_flash))))
