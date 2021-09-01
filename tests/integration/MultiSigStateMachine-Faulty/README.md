# Injecting Failures into MultiSig

This test case consists in injecting a bug into the MultiSig contract then detecting it in
of two different ways. 

## The Bug

The `FaultyMultiSig.*` files were obtained from the regular `MultiSigStateMachine` contract with
the follownig patch applied to it:

```patch
@@ -176,7 +176,7 @@ proposalExpired TxInfo{txInfoValidRange} Payment{paymentDeadline} =
 --   have signed a proposed payment.
 proposalAccepted :: Params -> [PubKeyHash] -> Bool
 proposalAccepted (Params signatories numReq) pks =
-    let numSigned = length (filter (\pk -> containsPk pk pks) signatories)
+    let numSigned = length (filter (\pk -> containsPk pk signatories) pks)
     in numSigned >= numReq
 
 {-# INLINABLE valuePreserved #-}
@@ -204,7 +204,7 @@ transition params State{ stateData =s, stateValue=currentValue} i = case (s, i)
                     }
                  )
     (CollectingSignatures pmt pks, AddSignature pk)
-        | isSignatory pk params && not (containsPk pk pks) ->
+        | isSignatory pk params ->
             let constraints = Constraints.mustBeSignedBy pk in
             Just ( constraints
                  , State
```

This patch makes it so that the contract stops checking for duplicate signatures, meaning that
a user could repeatedly add her own signature then issue a payment.

## Finding the Bug with a Refinement Spec

Because we want to use the same spec we're using for the real `MultiSigStateMachine`, we symlink
to the same skeleton and spec file. Running `tlc Contract_MC` will find a trace where
the same signature is used twice.

## Finding the Bug with a Correctness Property

Checking refinments is slow. Therefore, we also added a `PayCorrect` property to
`Contract_MC.tla`:

```tlaplus
PayCorrect == [](ENABLED ActionPay => Cardinality(ListToSet(st.arg0.arg1)) >= param.arg1)
```

Altering the property we ask TLC to check in `Contract_MC.cfg` to `PayCorrect` will speed up the
checking by an order of magnitude. It is worth keeping in mind that even if in this case one
could argue this is an obvious correctness property we want, we would still have to have the inspiration
to write this property explicitely. When checking the implementation against the refinement 
specification this correctness property was made implicit by utilizing a set to store signatures.
