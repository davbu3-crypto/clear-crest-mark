;; ClearCrestMark - Zero-Knowledge Academic Credential Verification

;; This contract manages:
;;   - Institution registration and staking
;;   - Credential issuance with cryptographic commitments
;;   - Selective disclosure and zk proof verification stubs
;;   - Micro-credential / skill badge stacking
;;   - Privacy-preserving job matching
;;   - Decentralized dispute resolution

;; ============================================================
;; CONSTANTS
;; ============================================================

(define-constant CONTRACT-OWNER tx-sender)

(define-constant ERR-NOT-AUTHORIZED        (err u100))
(define-constant ERR-ALREADY-REGISTERED   (err u101))
(define-constant ERR-NOT-REGISTERED       (err u102))
(define-constant ERR-INSUFFICIENT-STAKE   (err u103))
(define-constant ERR-CREDENTIAL-EXISTS    (err u104))
(define-constant ERR-CREDENTIAL-NOT-FOUND (err u105))
(define-constant ERR-INVALID-PROOF        (err u106))
(define-constant ERR-DISPUTE-NOT-FOUND    (err u107))
(define-constant ERR-ALREADY-VOTED        (err u108))
(define-constant ERR-MATCH-NOT-FOUND      (err u109))
(define-constant ERR-INVALID-PARAMS       (err u110))

;; Minimum STX stake required for institution registration (in micro-STX)
(define-constant MIN-INSTITUTION-STAKE u1000000000)

;; Dispute voting window in blocks (~7 days at ~10 min/block)
(define-constant DISPUTE-VOTING-BLOCKS u1008)

;; ============================================================
;; DATA MAPS AND VARS
;; ============================================================

;; Tracks total credentials issued
(define-data-var credential-nonce uint u0)

;; Tracks total disputes opened
(define-data-var dispute-nonce uint u0)

;; Tracks total job-match proposals
(define-data-var match-nonce uint u0)

;; --- Institutions ---
;; Stores registered academic institutions
(define-map institutions
  { institution: principal }
  {
    name:               (string-ascii 128),
    accreditation-level: uint,       ;; 1=basic, 2=regional, 3=national
    stake:              uint,        ;; staked micro-STX
    reputation-score:   uint,        ;; 0-1000 oracle-updated score
    is-active:          bool,
    registered-at:      uint
  }
)

;; --- Credentials ---
;; Merkle-commitment-based credential records
(define-map credentials
  { credential-id: uint }
  {
    holder:          principal,
    institution:     principal,
    ;; keccak/sha256 commitment of the full credential data (off-chain)
    commitment:      (buff 32),
    ;; credential type: 1=degree, 2=certificate, 3=micro-credential
    credential-type: uint,
    ;; nullifier prevents double-issuance of the same credential
    nullifier:       (buff 32),
    issued-at:       uint,
    is-revoked:      bool
  }
)

;; Nullifier registry - prevents duplicate credential commitments
(define-map nullifier-registry
  { nullifier: (buff 32) }
  { used: bool }
)

;; Holder credential index - maps holder to list of credential IDs
;; Stores up to 20 credential IDs per holder
(define-map holder-credentials
  { holder: principal }
  { ids: (list 20 uint) }
)

;; --- Skill Badges (micro-credential stacks) ---
(define-map skill-badges
  { badge-id: uint }
  {
    holder:       principal,
    ;; ordered list of up to 10 credential IDs that compose this badge
    credential-ids: (list 10 uint),
    skill-name:   (string-ascii 64),
    issued-at:    uint
  }
)

(define-data-var badge-nonce uint u0)

;; --- Job Matches ---
;; Privacy-preserving match proposals (identity hidden until mutual consent)
(define-map job-matches
  { match-id: uint }
  {
    ;; commitment hash of employer identity (revealed on consent)
    employer-commitment: (buff 32),
    ;; commitment hash of candidate identity
    candidate-commitment: (buff 32),
    ;; commitment hash of required-skill criteria
    skill-criteria-hash: (buff 32),
    employer-consented:  bool,
    candidate-consented: bool,
    ;; actual principals - only populated after mutual consent
    employer:   (optional principal),
    candidate:  (optional principal),
    created-at: uint
  }
)

;; --- Disputes ---
(define-map disputes
  { dispute-id: uint }
  {
    credential-id:   uint,
    complainant:     principal,
    reason-hash:     (buff 32),   ;; hash of off-chain dispute reason
    votes-valid:     uint,
    votes-invalid:   uint,
    resolved:        bool,
    outcome-valid:   bool,
    opened-at:       uint
  }
)

;; Tracks which institution has voted on a dispute
(define-map dispute-votes
  { dispute-id: uint, voter: principal }
  { voted: bool }
)

;; ============================================================
;; PRIVATE HELPERS
;; ============================================================

;; Check that a principal is a registered active institution
(define-private (is-active-institution (inst principal))
  (match (map-get? institutions { institution: inst })
    data (get is-active data)
    false
  )
)

;; Append a credential-id to the holder's index list
(define-private (push-credential-for-holder (holder principal) (cred-id uint))
  (let (
    (current (default-to { ids: (list) }
               (map-get? holder-credentials { holder: holder })))
    (new-ids (unwrap-panic (as-max-len?
               (append (get ids current) cred-id) u20)))
  )
    (map-set holder-credentials { holder: holder } { ids: new-ids })
  )
)

;; ============================================================
;; INSTITUTION MANAGEMENT
;; ============================================================

;; Register a new institution with an initial STX stake
(define-public (register-institution
    (name (string-ascii 128))
    (accreditation-level uint))
  (let (
    (stake-amount (stx-get-balance tx-sender))
  )
    (asserts! (is-none (map-get? institutions { institution: tx-sender }))
              ERR-ALREADY-REGISTERED)
    (asserts! (>= stake-amount MIN-INSTITUTION-STAKE)
              ERR-INSUFFICIENT-STAKE)
    (asserts! (and (>= accreditation-level u1) (<= accreditation-level u3))
              ERR-INVALID-PARAMS)
    ;; Transfer stake to contract
    (try! (stx-transfer? MIN-INSTITUTION-STAKE tx-sender (as-contract tx-sender)))
    (map-set institutions
      { institution: tx-sender }
      {
        name:               name,
        accreditation-level: accreditation-level,
        stake:              MIN-INSTITUTION-STAKE,
        reputation-score:   u500,
        is-active:          true,
        registered-at:      block-height
      }
    )
    (ok true)
  )
)

;; Allow an institution to top-up its stake
(define-public (add-stake (amount uint))
  (let (
    (inst-data (unwrap! (map-get? institutions { institution: tx-sender })
                        ERR-NOT-REGISTERED))
  )
    (asserts! (get is-active inst-data) ERR-NOT-AUTHORIZED)
    (try! (stx-transfer? amount tx-sender (as-contract tx-sender)))
    (map-set institutions
      { institution: tx-sender }
      (merge inst-data { stake: (+ (get stake inst-data) amount) })
    )
    (ok true)
  )
)

;; Contract owner can update reputation score (oracle integration point)
(define-public (update-reputation (institution principal) (new-score uint))
  (let (
    (inst-data (unwrap! (map-get? institutions { institution: institution })
                        ERR-NOT-REGISTERED))
  )
    (asserts! (is-eq tx-sender CONTRACT-OWNER) ERR-NOT-AUTHORIZED)
    (asserts! (<= new-score u1000) ERR-INVALID-PARAMS)
    (map-set institutions
      { institution: institution }
      (merge inst-data { reputation-score: new-score })
    )
    (ok true)
  )
)

;; ============================================================
;; CREDENTIAL ISSUANCE
;; ============================================================

;; Issue a credential using a cryptographic commitment and nullifier
;; commitment  = sha256(holder || degree-data || salt) computed off-chain
;; nullifier   = sha256(institution-secret || commitment)  -- prevents re-issue
(define-public (issue-credential
    (holder principal)
    (commitment (buff 32))
    (nullifier (buff 32))
    (credential-type uint))
  (let (
    (cred-id (+ (var-get credential-nonce) u1))
  )
    ;; Only registered active institutions may issue
    (asserts! (is-active-institution tx-sender) ERR-NOT-AUTHORIZED)
    ;; Nullifier must be fresh
    (asserts! (is-none (map-get? nullifier-registry { nullifier: nullifier }))
              ERR-CREDENTIAL-EXISTS)
    (asserts! (and (>= credential-type u1) (<= credential-type u3))
              ERR-INVALID-PARAMS)
    ;; Record nullifier
    (map-set nullifier-registry { nullifier: nullifier } { used: true })
    ;; Store credential
    (map-set credentials
      { credential-id: cred-id }
      {
        holder:          holder,
        institution:     tx-sender,
        commitment:      commitment,
        credential-type: credential-type,
        nullifier:       nullifier,
        issued-at:       block-height,
        is-revoked:      false
      }
    )
    ;; Update holder index
    (push-credential-for-holder holder cred-id)
    (var-set credential-nonce cred-id)
    (ok cred-id)
  )
)

;; Revoke a previously issued credential
(define-public (revoke-credential (credential-id uint))
  (let (
    (cred (unwrap! (map-get? credentials { credential-id: credential-id })
                   ERR-CREDENTIAL-NOT-FOUND))
  )
    (asserts! (is-eq tx-sender (get institution cred)) ERR-NOT-AUTHORIZED)
    (map-set credentials
      { credential-id: credential-id }
      (merge cred { is-revoked: true })
    )
    (ok true)
  )
)

;; ============================================================
;; SELECTIVE DISCLOSURE / ZK PROOF VERIFICATION
;; ============================================================

;; Verify a zk-SNARK proof for a selective attribute disclosure.
;; In production this would call a Clarity-compatible verifier contract.
;; Here we record the intent and emit an event via the response.
;;
;; proof-hash    = off-chain generated proof (256-bit hash stub)
;; attribute-key = e.g. "gpa-range", "graduation-year"
;; public-input  = the publicly revealed value (e.g. GPA bucket index)
(define-public (verify-selective-disclosure
    (credential-id uint)
    (proof-hash (buff 32))
    (attribute-key (string-ascii 32))
    (public-input uint))
  (let (
    (cred (unwrap! (map-get? credentials { credential-id: credential-id })
                   ERR-CREDENTIAL-NOT-FOUND))
  )
    ;; Only the credential holder may disclose
    (asserts! (is-eq tx-sender (get holder cred)) ERR-NOT-AUTHORIZED)
    (asserts! (not (get is-revoked cred)) ERR-INVALID-PROOF)
    ;; --- zk verifier stub ---
    ;; A production implementation would call:
    ;;   (contract-call? .zk-verifier verify proof-hash public-input)
    ;; For now we accept non-zero proof hashes as valid
    (asserts! (not (is-eq proof-hash 0x0000000000000000000000000000000000000000000000000000000000000000))
              ERR-INVALID-PROOF)
    (ok {
      credential-id: credential-id,
      attribute:     attribute-key,
      public-input:  public-input,
      verified-at:   block-height
    })
  )
)

;; ============================================================
;; SKILL BADGE STACKING
;; ============================================================

;; Mint a portable skill badge by stacking up to 10 credentials
(define-public (mint-skill-badge
    (credential-ids (list 10 uint))
    (skill-name (string-ascii 64)))
  (let (
    (badge-id (+ (var-get badge-nonce) u1))
  )
    (asserts! (> (len credential-ids) u0) ERR-INVALID-PARAMS)
    (map-set skill-badges
      { badge-id: badge-id }
      {
        holder:         tx-sender,
        credential-ids: credential-ids,
        skill-name:     skill-name,
        issued-at:      block-height
      }
    )
    (var-set badge-nonce badge-id)
    (ok badge-id)
  )
)

;; ============================================================
;; PRIVACY-PRESERVING JOB MATCHING
;; ============================================================

;; Employer opens a match proposal using commitment hashes only
(define-public (propose-match
    (employer-commitment (buff 32))
    (candidate-commitment (buff 32))
    (skill-criteria-hash (buff 32)))
  (let (
    (match-id (+ (var-get match-nonce) u1))
  )
    (map-set job-matches
      { match-id: match-id }
      {
        employer-commitment:  employer-commitment,
        candidate-commitment: candidate-commitment,
        skill-criteria-hash:  skill-criteria-hash,
        employer-consented:   false,
        candidate-consented:  false,
        employer:             none,
        candidate:            none,
        created-at:           block-height
      }
    )
    (var-set match-nonce match-id)
    (ok match-id)
  )
)

;; Either party consents and reveals their identity
(define-public (consent-to-match (match-id uint) (role (string-ascii 10)))
  (let (
    (m (unwrap! (map-get? job-matches { match-id: match-id })
                ERR-MATCH-NOT-FOUND))
  )
    (asserts! (or (is-eq role "employer") (is-eq role "candidate"))
              ERR-INVALID-PARAMS)
    (if (is-eq role "employer")
      (map-set job-matches { match-id: match-id }
        (merge m { employer-consented: true, employer: (some tx-sender) }))
      (map-set job-matches { match-id: match-id }
        (merge m { candidate-consented: true, candidate: (some tx-sender) }))
    )
    (ok true)
  )
)

;; ============================================================
;; DISPUTE RESOLUTION
;; ============================================================

;; Open a dispute against a credential
(define-public (open-dispute
    (credential-id uint)
    (reason-hash (buff 32)))
  (let (
    (dispute-id (+ (var-get dispute-nonce) u1))
    (_cred (unwrap! (map-get? credentials { credential-id: credential-id })
                    ERR-CREDENTIAL-NOT-FOUND))
  )
    (map-set disputes
      { dispute-id: dispute-id }
      {
        credential-id:  credential-id,
        complainant:    tx-sender,
        reason-hash:    reason-hash,
        votes-valid:    u0,
        votes-invalid:  u0,
        resolved:       false,
        outcome-valid:  false,
        opened-at:      block-height
      }
    )
    (var-set dispute-nonce dispute-id)
    (ok dispute-id)
  )
)

;; Registered institutions vote on a dispute (peer jury)
;; vote: true = credential is valid, false = credential is invalid
(define-public (vote-on-dispute (dispute-id uint) (vote bool))
  (let (
    (d (unwrap! (map-get? disputes { dispute-id: dispute-id })
                ERR-DISPUTE-NOT-FOUND))
  )
    (asserts! (is-active-institution tx-sender) ERR-NOT-AUTHORIZED)
    (asserts! (not (get resolved d)) ERR-NOT-AUTHORIZED)
    (asserts! (< block-height (+ (get opened-at d) DISPUTE-VOTING-BLOCKS))
              ERR-NOT-AUTHORIZED)
    (asserts! (is-none (map-get? dispute-votes { dispute-id: dispute-id, voter: tx-sender }))
              ERR-ALREADY-VOTED)
    (map-set dispute-votes { dispute-id: dispute-id, voter: tx-sender } { voted: true })
    (if vote
      (map-set disputes { dispute-id: dispute-id }
        (merge d { votes-valid: (+ (get votes-valid d) u1) }))
      (map-set disputes { dispute-id: dispute-id }
        (merge d { votes-invalid: (+ (get votes-invalid d) u1) }))
    )
    (ok true)
  )
)

;; Resolve a dispute after the voting window has closed
(define-public (resolve-dispute (dispute-id uint))
  (let (
    (d (unwrap! (map-get? disputes { dispute-id: dispute-id })
                ERR-DISPUTE-NOT-FOUND))
    (outcome (> (get votes-valid d) (get votes-invalid d)))
  )
    (asserts! (not (get resolved d)) ERR-NOT-AUTHORIZED)
    (asserts! (>= block-height (+ (get opened-at d) DISPUTE-VOTING-BLOCKS))
              ERR-NOT-AUTHORIZED)
    ;; If majority ruled invalid, auto-revoke the credential
    (if (not outcome)
      (let (
        (cred (unwrap! (map-get? credentials { credential-id: (get credential-id d) })
                       ERR-CREDENTIAL-NOT-FOUND))
      )
        (map-set credentials
          { credential-id: (get credential-id d) }
          (merge cred { is-revoked: true }))
        true
      )
      true
    )
    (map-set disputes { dispute-id: dispute-id }
      (merge d { resolved: true, outcome-valid: outcome }))
    (ok outcome)
  )
)

;; ============================================================
;; READ-ONLY QUERIES
;; ============================================================

(define-read-only (get-institution (institution principal))
  (map-get? institutions { institution: institution })
)

(define-read-only (get-credential (credential-id uint))
  (map-get? credentials { credential-id: credential-id })
)

(define-read-only (get-holder-credentials (holder principal))
  (default-to { ids: (list) }
    (map-get? holder-credentials { holder: holder }))
)

(define-read-only (get-skill-badge (badge-id uint))
  (map-get? skill-badges { badge-id: badge-id })
)

(define-read-only (get-job-match (match-id uint))
  (map-get? job-matches { match-id: match-id })
)

(define-read-only (get-dispute (dispute-id uint))
  (map-get? disputes { dispute-id: dispute-id })
)

(define-read-only (is-nullifier-used (nullifier (buff 32)))
  (is-some (map-get? nullifier-registry { nullifier: nullifier }))
)

(define-read-only (get-total-credentials)
  (var-get credential-nonce)
)

(define-read-only (get-total-disputes)
  (var-get dispute-nonce)
)

(define-read-only (get-total-matches)
  (var-get match-nonce)
)
