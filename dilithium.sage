#!/usr/bin/env python3
"""
Dilithium Post-Quantum Digital Signature Scheme Implementation
Security Level 5 Parameters
"""

import os
from hashlib import shake_256
from sage.all import *

# ============================================================================
# DILITHIUM SECURITY LEVEL 5 CONFIGURATION
# ============================================================================

class DilithiumConfig:
    """Configuration parameters for Dilithium Level 5"""
    
    # Matrix dimensions
    ROWS = 8           # k - number of rows in matrix A
    COLS = 7           # l - number of columns in matrix A
    
    # Security parameters
    ETA_BOUND = 2      # eta - bound for secret key coefficients
    POWER_OF_TWO = 13  # d - power of 2 for rounding
    POLY_DEGREE = 256  # n - degree of polynomials
    
    # Prime modulus
    PRIME_Q = 8380417  # q = 2^23 - 2^13 + 1
    
    # Rejection sampling bounds
    GAMMA_1 = 2**19                    # gamma1 - bound for masking vector
    GAMMA_2 = (PRIME_Q - 1) // 32     # gamma2 - bound for decomposition
    
    # Challenge parameters
    TAU_WEIGHT = 60                    # tau - weight of challenge polynomial
    BETA_THRESHOLD = 60 * ETA_BOUND    # beta - rejection threshold
    OMEGA_LIMIT = 75                   # omega - maximum hint weight

# ============================================================================
# CRYPTOGRAPHIC PRIMITIVES AND UTILITIES
# ============================================================================

def shake256_hash(input_data, output_length):
    hasher = shake_256(input_data)
    return hasher.digest(output_length)

def collision_resistant_hash(input_data, output_length):
    return shake256_hash(input_data, output_length)

def generate_matrix_from_seed(seed_rho, rows, cols, poly_degree, polynomial_ring, modulus_q):
    matrix_elements = []
    
    for i in range(rows):
        for j in range(cols):
            # Create unique seed for each matrix element
            element_seed = seed_rho + i.to_bytes(1, 'big') + j.to_bytes(1, 'big')
            hash_output = shake256_hash(element_seed, poly_degree * 4)  # 4 bytes per coefficient
            
            coefficients = []
            for k in range(poly_degree):
                # Extract 4 bytes and convert to coefficient
                coeff_bytes = hash_output[k*4:(k+1)*4]
                coeff_val = int.from_bytes(coeff_bytes, 'big') % modulus_q
                coefficients.append(coeff_val)
            
            matrix_elements.append(polynomial_ring(coefficients))
    
    return Matrix(polynomial_ring, rows, cols, matrix_elements)

def power_of_two_decomposition(polynomial, power_d, ring_rq, modulus_q):
    """
    Decompose polynomial coefficients into high and low parts
    using power of 2 rounding
    """
    coefficients = polynomial.list()
    high_parts, low_parts = [], []
    half_power = 2**power_d // 2
    
    for coeff in coefficients:
        coeff_int = Integer(coeff.lift())
        if coeff_int > modulus_q // 2:
            coeff_int -= modulus_q
        
        low_part = ((coeff_int + half_power) % (2**power_d)) - half_power
        high_part = (coeff_int - low_part) // (2**power_d)
        
        high_parts.append(Zmod(modulus_q)(high_part))
        low_parts.append(Zmod(modulus_q)(low_part))
    
    return ring_rq(high_parts), ring_rq(low_parts)

def coefficient_decomposition(polynomial, gamma_2, ring_rq, modulus_q):
    """
    Decompose polynomial v = v_high * gamma2 + v_low
    where |v_low| <= gamma2
    """
    coefficients = polynomial.list()
    high_coeffs, low_coeffs = [], []
    
    for coeff in coefficients:
        coeff_int = Integer(coeff.lift())
        if coeff_int > modulus_q // 2:
            coeff_int -= modulus_q
        
        high_coeff = (coeff_int + gamma_2) // (2 * gamma_2)
        low_coeff = coeff_int - high_coeff * (2 * gamma_2)
        
        high_coeffs.append(Zmod(modulus_q)(high_coeff))
        low_coeffs.append(Zmod(modulus_q)(low_coeff))
    
    return ring_rq(high_coeffs), ring_rq(low_coeffs)

def extract_high_bits(polynomial, gamma_2, ring_rq, modulus_q):
    """Extract high-order bits from polynomial decomposition"""
    high_part, _ = coefficient_decomposition(polynomial, gamma_2, ring_rq, modulus_q)
    return high_part

def extract_low_bits(polynomial, gamma_2, ring_rq, modulus_q):
    """Extract low-order bits from polynomial decomposition"""
    _, low_part = coefficient_decomposition(polynomial, gamma_2, ring_rq, modulus_q)
    return low_part

def generate_challenge_polynomial(seed, tau_weight, poly_degree, ring_rq, modulus_q):
    """
    Generate sparse challenge polynomial with exactly tau_weight non-zero coefficients
    """
    hasher = shake_256(seed)
    random_bytes = hasher.digest(8 * tau_weight)  # More bytes for safety
    
    # Extract sign bits
    sign_bits = [(random_bytes[i // 8] >> (i % 8)) & 1 for i in range(tau_weight)]
    
    # Extract unique positions
    selected_positions = []
    byte_index = 0
    
    while len(selected_positions) < tau_weight and byte_index < len(random_bytes) - 1:
        position = Integer(int.from_bytes(
            random_bytes[2 * byte_index:2 * byte_index + 2], 'big'
        )) % poly_degree
        
        if position not in selected_positions:
            selected_positions.append(position)
        
        byte_index += 1
    
    # If we don't have enough positions, pad with remaining
    while len(selected_positions) < tau_weight:
        for i in range(poly_degree):
            if i not in selected_positions:
                selected_positions.append(i)
                if len(selected_positions) >= tau_weight:
                    break
    
    # Construct challenge polynomial
    polynomial_coeffs = [0] * poly_degree
    for idx, position in enumerate(selected_positions[:tau_weight]):
        polynomial_coeffs[position] = 1 if sign_bits[idx] == 0 else -1
    
    return ring_rq([Zmod(modulus_q)(c) for c in polynomial_coeffs])

def infinity_norm(vector, modulus_q):
    """
    Compute infinity norm of a vector of polynomials
    """
    maximum_norm = 0
    half_modulus = modulus_q // 2
    
    for polynomial in vector:
        for coefficient in polynomial.list():
            coeff_val = int(coefficient.lift())
            if coeff_val > half_modulus:
                coeff_val -= modulus_q
            
            maximum_norm = max(maximum_norm, abs(coeff_val))
    
    return maximum_norm

def create_hint_polynomial(poly_f, poly_g, gamma_2, ring_rq, modulus_q):
    """
    Create hint polynomial indicating where high bits differ
    """
    high_f = extract_high_bits(poly_f, gamma_2, ring_rq, modulus_q)
    high_g = extract_high_bits(poly_g, gamma_2, ring_rq, modulus_q)
    
    hint_coeffs = [
        Zmod(modulus_q)(1 if coeff_a != coeff_b else 0)
        for coeff_a, coeff_b in zip(high_f.list(), high_g.list())
    ]
    
    return ring_rq(hint_coeffs)

def apply_hint_correction(low_poly, high_poly, hint_poly, ring_rq, modulus_q):
    """
    Apply hint to correct high-order bits
    """
    low_coeffs = [int(c.lift()) for c in low_poly.list()]
    high_coeffs = [int(c.lift()) for c in high_poly.list()]
    hint_coeffs = [int(c.lift()) for c in hint_poly.list()]
    
    half_modulus = modulus_q // 2
    corrected_coeffs = []
    
    for low_c, high_c, hint_c in zip(low_coeffs, high_coeffs, hint_coeffs):
        if low_c > half_modulus:
            low_c -= modulus_q
        
        if hint_c == 0:
            corrected_coeffs.append(Zmod(modulus_q)(high_c))
        else:
            correction = 1 if low_c > 0 else -1
            corrected_coeffs.append(Zmod(modulus_q)(high_c + correction))
    
    return ring_rq(corrected_coeffs)

def pack_high_bits(polynomial_vector, gamma_2, modulus_q):
    """
    Pack high-order bits into byte array for hashing
    """
    all_coefficients = []
    
    for polynomial in polynomial_vector:
        for coefficient in polynomial.list():
            coeff_int = Integer(coefficient.lift())
            if coeff_int > modulus_q // 2:
                coeff_int -= modulus_q
            
            all_coefficients.append(coeff_int & 0xF)
    
    # Pack pairs of 4-bit values into bytes
    packed_bytes = []
    for i in range(0, len(all_coefficients), 2):
        lower_nibble = all_coefficients[i]
        upper_nibble = all_coefficients[i + 1] if i + 1 < len(all_coefficients) else 0
        packed_byte = lower_nibble | (upper_nibble << 4)
        packed_bytes.append(packed_byte)
    
    return bytes(packed_bytes)

# ============================================================================
# DILITHIUM SIGNATURE SCHEME
# ============================================================================

class DilithiumSigner:
    """Dilithium Post-Quantum Digital Signature Implementation"""
    
    def __init__(self):
        self.config = DilithiumConfig()
        
        # Initialize polynomial ring
        base_ring = PolynomialRing(Zmod(self.config.PRIME_Q), 'x')
        self.polynomial_ring = base_ring.quotient(
            base_ring.gen()**self.config.POLY_DEGREE + 1, 'r'
        )
    
    def generate_keypair(self):
        """
        Generate Dilithium public and private key pair
        Returns: (public_key, private_key)
        """
        print("Generating Dilithium keypair...")
        
        # Generate master seed
        master_seed = os.urandom(32)
        
        # Derive seeds using hash expansion
        expanded_seeds = shake256_hash(master_seed, 3 * 32)
        seed_rho = expanded_seeds[0:32]
        seed_sigma = expanded_seeds[32:64] 
        seed_key = expanded_seeds[64:96]
        
        # Generate secret vectors s1 and s2
        secret_s1 = [
            self.polynomial_ring([
                ZZ.random_element(-self.config.ETA_BOUND, self.config.ETA_BOUND)
                for _ in range(self.config.POLY_DEGREE)
            ])
            for _ in range(self.config.COLS)
        ]
        
        secret_s2 = [
            self.polynomial_ring([
                ZZ.random_element(-self.config.ETA_BOUND, self.config.ETA_BOUND)
                for _ in range(self.config.POLY_DEGREE)
            ])
            for _ in range(self.config.ROWS)
        ]
        
        # Generate matrix A deterministically from seed_rho
        matrix_a = generate_matrix_from_seed(
            seed_rho, self.config.ROWS, self.config.COLS,
            self.config.POLY_DEGREE, self.polynomial_ring, self.config.PRIME_Q
        )
        
        # Compute t = A*s1 + s2
        vector_t = matrix_a * vector(secret_s1) + vector(secret_s2)
        
        # Power-of-2 decomposition of t
        t_high = vector([
            power_of_two_decomposition(
                poly, self.config.POWER_OF_TWO, 
                self.polynomial_ring, self.config.PRIME_Q
            )[0] 
            for poly in vector_t
        ])
        
        t_low = vector([
            power_of_two_decomposition(
                poly, self.config.POWER_OF_TWO,
                self.polynomial_ring, self.config.PRIME_Q
            )[1]
            for poly in vector_t
        ])
        
        # Compute public key hash
        public_key_hash = collision_resistant_hash(
            seed_rho + pack_high_bits(t_high, self.config.GAMMA_2, self.config.PRIME_Q),
            48
        )
        
        public_key = (seed_rho, t_high)
        private_key = (seed_rho, seed_key, public_key_hash, secret_s1, secret_s2, t_low, matrix_a)
        
        print("Keypair generation completed")
        return public_key, private_key
    
    def sign_message(self, private_key, message):
        """
        Generate digital signature for given message
        """
        print(f"Signing message: {message}")
        
        seed_rho, seed_key, pk_hash, secret_s1, secret_s2, t_low, matrix_a = private_key
        
        # Compute message hash
        message_hash = collision_resistant_hash(pk_hash + message, 48)
        
        attempt_counter = 0
        
        while True:
            # Generate masking vector y
            masking_y = [
                self.polynomial_ring([
                    ZZ.random_element(-self.config.GAMMA_1 + 1, self.config.GAMMA_1 - 1)
                    for _ in range(self.config.POLY_DEGREE)
                ])
                for _ in range(self.config.COLS)
            ]
            
            # Compute w = A*y
            vector_w = matrix_a * vector(self.polynomial_ring, masking_y)
            
            # Decompose w into high and low parts
            w_high = vector(self.polynomial_ring, [
                extract_high_bits(wi, self.config.GAMMA_2, self.polynomial_ring, self.config.PRIME_Q)
                for wi in vector_w
            ])
            
            w_low = vector(self.polynomial_ring, [
                extract_low_bits(wi, self.config.GAMMA_2, self.polynomial_ring, self.config.PRIME_Q)
                for wi in vector_w
            ])
            
            # Generate challenge polynomial
            challenge_seed = message_hash + pack_high_bits(w_high, self.config.GAMMA_2, self.config.PRIME_Q)
            challenge_c = generate_challenge_polynomial(
                challenge_seed, self.config.TAU_WEIGHT, self.config.POLY_DEGREE,
                self.polynomial_ring, self.config.PRIME_Q
            )
            
            # Compute signature candidate z = y + c*s1
            signature_z = vector(self.polynomial_ring, masking_y) + challenge_c * vector(self.polynomial_ring, secret_s1)
            z_norm = infinity_norm(signature_z, self.config.PRIME_Q)
            
            # Compute r0 = w_low - c*s2
            remainder_r0 = w_low - challenge_c * vector(self.polynomial_ring, secret_s2)
            r0_norm = infinity_norm(remainder_r0, self.config.PRIME_Q)
            
            # First rejection sampling check
            if z_norm >= (self.config.GAMMA_1 - self.config.BETA_THRESHOLD) or \
               r0_norm >= (self.config.GAMMA_2 - self.config.BETA_THRESHOLD):
                attempt_counter += 1
                if attempt_counter % 10 == 0:
                    print(f"Rejection sampling: attempt {attempt_counter}...")
                continue
            
            # Generate hint vector
            hint_vector = []
            for i in range(self.config.ROWS):
                hint_f = -challenge_c * t_low[i]
                hint_g = remainder_r0[i] + (challenge_c * t_low[i])
                hint_vector.append(
                    create_hint_polynomial(
                        hint_f, hint_g, self.config.GAMMA_2,
                        self.polynomial_ring, self.config.PRIME_Q
                    )
                )
            
            hint_h = vector(self.polynomial_ring, hint_vector)
            
            # Second rejection sampling check
            ct0_norm = infinity_norm(
                vector(self.polynomial_ring, [challenge_c * poly for poly in t_low]),
                self.config.PRIME_Q
            )
            
            hint_weight = sum(
                1 for poly in hint_h 
                for coeff in poly.list() 
                if int(coeff) == 1
            )
            
            if ct0_norm >= self.config.GAMMA_2 or hint_weight > self.config.OMEGA_LIMIT:
                attempt_counter += 1
                if attempt_counter % 10 == 0:
                    print(f"Rejection sampling: attempt {attempt_counter}...")
                continue
            
            signature = (signature_z, hint_h, challenge_c)
            print(f"Signature generated after {attempt_counter + 1} attempts")
            return signature
    
    def verify_signature(self, public_key, message, signature):
        """
        Verify digital signature
        Returns: True if valid, False otherwise
        """
        print("Verifying signature...")
        
        seed_rho, t_high = public_key
        signature_z, hint_h, challenge_c = signature
        
        # Recompute public key hash
        pk_hash = collision_resistant_hash(
            seed_rho + pack_high_bits(t_high, self.config.GAMMA_2, self.config.PRIME_Q),
            48
        )
        
        # Recompute message hash
        message_hash = collision_resistant_hash(pk_hash + message, 48)
        
        # Check signature norm
        z_norm = infinity_norm(signature_z, self.config.PRIME_Q)
        if z_norm >= (self.config.GAMMA_1 - self.config.BETA_THRESHOLD):
            print("Verification failed: signature norm too large")
            return False
        
        # Regenerate matrix A deterministically
        matrix_a = generate_matrix_from_seed(
            seed_rho, self.config.ROWS, self.config.COLS,
            self.config.POLY_DEGREE, self.polynomial_ring, self.config.PRIME_Q
        )
        
        # Compute Az
        az_result = matrix_a * signature_z
        
        # Scale t_high by 2^d
        t_high_scaled = [poly * (2**self.config.POWER_OF_TWO) for poly in t_high]
        ct_high = challenge_c * vector(self.polynomial_ring, t_high_scaled)
        
        # Compute w' = Az - c*t_high*2^d
        w_prime = vector(self.polynomial_ring, [
            (az_result[i] - ct_high[i]) for i in range(self.config.ROWS)
        ])
        
        # Decompose w'
        w_prime_high = vector(self.polynomial_ring, [
            extract_high_bits(wi, self.config.GAMMA_2, self.polynomial_ring, self.config.PRIME_Q)
            for wi in w_prime
        ])
        
        w_prime_low = vector(self.polynomial_ring, [
            extract_low_bits(wi, self.config.GAMMA_2, self.polynomial_ring, self.config.PRIME_Q)
            for wi in w_prime
        ])
        
        # Check hint weight
        hint_weight = sum(
            1 for poly in hint_h
            for coeff in poly.list()
            if int(coeff) == 1
        )
        
        if hint_weight > self.config.OMEGA_LIMIT:
            print("Verification failed: hint weight too large")
            return False
        
        # Apply hint correction
        w_corrected = vector(self.polynomial_ring, [
            apply_hint_correction(
                w_prime_low[i], w_prime_high[i], hint_h[i],
                self.polynomial_ring, self.config.PRIME_Q
            )
            for i in range(self.config.ROWS)
        ])
        
        # Recompute challenge
        verification_seed = message_hash + pack_high_bits(w_corrected, self.config.GAMMA_2, self.config.PRIME_Q)
        challenge_verification = generate_challenge_polynomial(
            verification_seed, self.config.TAU_WEIGHT, self.config.POLY_DEGREE,
            self.polynomial_ring, self.config.PRIME_Q
        )
        
        # Final verification check
        if challenge_c != challenge_verification:
            print("Verification failed: challenge mismatch")
            return False
        
        print("Signature verification successful")
        return True

# ============================================================================
# DEMONSTRATION AND TESTING
# ============================================================================

def main():
    """Demonstrate Dilithium signature scheme"""
    print("=" * 60)
    print("DILITHIUM POST-QUANTUM SIGNATURE DEMONSTRATION")
    print("=" * 60)
    print()
    
    dilithium = DilithiumSigner()
    
    public_key, private_key = dilithium.generate_keypair()
    print()
    
    test_message = b"Post-quantum cryptography with Dilithium!"
    signature = dilithium.sign_message(private_key, test_message)
    print()
    
    is_valid = dilithium.verify_signature(public_key, test_message, signature)
    print()
    
    print("Testing with tampered message...")
    tampered_message = b"Post-quantum cryptography with Dilithium?"
    is_tampered_valid = dilithium.verify_signature(public_key, tampered_message, signature)
    print()
    
    print("=" * 60)
    print("DEMONSTRATION COMPLETE")
    print(f"Original message verification: {'PASSED' if is_valid else 'FAILED'}")
    print(f"Tampered message verification: {'PASSED' if is_tampered_valid else 'FAILED'}")
    print("=" * 60)

if __name__ == "__main__":
    main()