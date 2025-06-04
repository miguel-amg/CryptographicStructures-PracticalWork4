from random import shuffle
import numpy as np
from cryptography.hazmat.primitives import hashes
from sage.rings.finite_rings.finite_field_constructor import GF
from sage.rings.polynomial.polynomial_ring_constructor import PolynomialRing
from sage.rings.quotient_ring import QuotientRing
from sage.modules.free_module import VectorSpace
from sage.matrix.constructor import Matrix
from sage.matrix.special import block_matrix

# Ring initialization and parameter setup
block_size = 257  # Block dimension
error_weight = 16   # Error vector weight
total_length = 2 * block_size  # Complete vector size
field_base = GF(2)
poly_ring = PolynomialRing(field_base, name='w')
w = poly_ring.gen()
quotient_ring = QuotientRing(poly_ring, poly_ring.ideal(w^block_size + 1))

def generate_sparse_polynomial(density=3):
    """Creates sparse polynomial with 'density' non-zero coefficients."""
    coefficient_list = [1] * density + [0] * (block_size - 2 - density)
    shuffle(coefficient_list)
    return quotient_ring([1] + coefficient_list + [1])

def create_error_vectors(weight):
    """Creates two error polynomials with combined weight."""
    elements = [1] * weight + [0] * (total_length - weight)
    shuffle(elements)
    return quotient_ring(elements[:block_size]), quotient_ring(elements[block_size:])

def compute_hash(first_poly, second_poly):
    """Computes SHA256 hash of two polynomials."""
    hasher = hashes.Hash(hashes.SHA256())
    hasher.update(str(first_poly).encode())
    hasher.update(str(second_poly).encode())
    return hasher.finalize()

def polynomial_to_vector_r(polynomial):
    """Converts polynomial to vector of size block_size."""
    vector_space = VectorSpace(field_base, block_size)
    return vector_space(polynomial.list() + [0] * (block_size - len(polynomial.list())))

def polynomial_pair_to_vector_n(cipher_pair):
    """Converts polynomial pair to vector of size total_length."""
    vector_space = VectorSpace(field_base, total_length)
    combined_list = polynomial_to_vector_r(cipher_pair[0]).list() + polynomial_to_vector_r(cipher_pair[1]).list()
    return vector_space(combined_list)

def rotate_vector(input_vector):
    """Rotates vector by one position."""
    vector_space = VectorSpace(field_base, block_size)
    output_vector = vector_space()
    output_vector[0] = input_vector[-1]
    for idx in range(block_size - 1):
        output_vector[idx + 1] = input_vector[idx]
    return output_vector

def build_rotation_matrix(polynomial):
    """Builds rotation matrix from polynomial."""
    matrix = Matrix(field_base, block_size, block_size)
    matrix[0] = polynomial_to_vector_r(polynomial)
    for row_idx in range(1, block_size):
        matrix[row_idx] = rotate_vector(matrix[row_idx - 1])
    return matrix

def calculate_hamming_weight(vector):
    """Computes Hamming weight of vector."""
    return sum([1 if element == 1 else 0 for element in vector])

def iterative_bit_correction(parity_matrix, received_vector, syndrome):
    """Bit-flipping algorithm for error correction."""
    current_guess = received_vector
    current_syndrome = syndrome
    max_iterations = block_size
    while calculate_hamming_weight(current_syndrome) > 0 and max_iterations > 0:
        max_iterations -= 1
        error_weights = [calculate_hamming_weight(current_syndrome.pairwise_product(parity_matrix[i])) for i in range(total_length)]
        peak_weight = max(error_weights)
        for position in range(total_length):
            if error_weights[position] == peak_weight:
                current_guess[position] = 1 - current_guess[position]
                current_syndrome += parity_matrix[position]
    if max_iterations == 0:
        print("Bit-Correction: Maximum iterations reached")
        return None
    return current_guess

def generate_key_pair():
    """Generates public-private key pair."""
    secret_poly_1 = generate_sparse_polynomial()
    secret_poly_2 = generate_sparse_polynomial()
    private_key = (secret_poly_1, secret_poly_2)
    public_key = (1, secret_poly_1 / secret_poly_2)
    print(f"Public key generated: {public_key}")
    return private_key, public_key

def encapsulate_secret(public_key):
    """Encapsulates a shared secret."""
    error_1, error_2 = create_error_vectors(error_weight)
    shared_secret = compute_hash(error_1, error_2)
    random_element = quotient_ring.random_element()
    ciphertext = (random_element * public_key[0] + error_1, random_element * public_key[1] + error_2)
    print(f"Secret encapsulated: {shared_secret.hex()}")
    print(f"Ciphertext created: {ciphertext}")
    return shared_secret, ciphertext

def decapsulate_secret(private_key, ciphertext):
    """Decapsulates the shared secret."""
    rotation_matrix_1 = build_rotation_matrix(private_key[0])
    rotation_matrix_2 = build_rotation_matrix(private_key[1])
    parity_check = block_matrix(2, 1, [rotation_matrix_1, rotation_matrix_2])
    cipher_vector = polynomial_pair_to_vector_n(ciphertext)
    syndrome_vector = cipher_vector * parity_check
    corrected_error = iterative_bit_correction(parity_check, cipher_vector, syndrome_vector)
    if corrected_error is None:
        print("Decapsulate: Iteration limit reached")
        return None
    error_list = corrected_error.list()
    recovered_error_1 = quotient_ring(error_list[:block_size])
    recovered_error_2 = quotient_ring(error_list[block_size:])
    original_error_1 = ciphertext[0] - recovered_error_1
    original_error_2 = ciphertext[1] - recovered_error_2
    if calculate_hamming_weight(polynomial_to_vector_r(original_error_1)) + calculate_hamming_weight(polynomial_to_vector_r(original_error_2)) != error_weight:
        print("Decapsulate: Decoding error detected")
        return None
    recovered_secret = compute_hash(original_error_1, original_error_2)
    print(f"Secret decapsulated: {recovered_secret.hex()}")
    return recovered_secret

# PKE implementation with Fujisaki-Okamoto transform
def hash_function_g(input_element):
    """Hash function g for transformation."""
    hasher = hashes.Hash(hashes.SHA256())
    hasher.update(str(input_element).encode())
    return hasher.finalize()

def xor_operation(data_bytes, mask_bytes):
    """XOR operation with mask repetition."""
    output = b''
    data_len = len(data_bytes)
    mask_len = len(mask_bytes)
    byte_index = 0
    while byte_index < data_len:
        for mask_index in range(mask_len):
            if byte_index < data_len:
                output += (data_bytes[byte_index] ^^ mask_bytes[mask_index]).to_bytes(1, byteorder='big')
                byte_index += 1
            else:
                break
    return output

def encryption_function_f(public_key, message_poly, error_1, error_2):
    """Function f for PKE scheme."""
    ciphertext_pair = (message_poly * public_key[0] + error_1, message_poly * public_key[1] + error_2)
    derived_key = compute_hash(error_1, error_2)
    return derived_key, ciphertext_pair

def extract_errors_from_ciphertext(private_key, error_ciphertext):
    """Extracts errors from ciphertext."""
    rotation_matrix_1 = build_rotation_matrix(private_key[0])
    rotation_matrix_2 = build_rotation_matrix(private_key[1])
    parity_check = block_matrix(2, 1, [rotation_matrix_1, rotation_matrix_2])
    error_vector = polynomial_pair_to_vector_n(error_ciphertext)
    syndrome_vector = error_vector * parity_check
    corrected_error = iterative_bit_correction(parity_check, error_vector, syndrome_vector)
    if corrected_error is None:
        print("ExtractErrors: Iteration limit reached")
        return None
    error_list = corrected_error.list()
    recovered_error_1 = quotient_ring(error_list[:block_size])
    recovered_error_2 = quotient_ring(error_list[block_size:])
    original_error_1 = error_ciphertext[0] - recovered_error_1
    original_error_2 = error_ciphertext[1] - recovered_error_2
    return original_error_1, original_error_2

def derive_key_from_errors(error_1, error_2):
    """Derives key from error polynomials."""
    if calculate_hamming_weight(polynomial_to_vector_r(error_1)) + calculate_hamming_weight(polynomial_to_vector_r(error_2)) != error_weight:
        print("DeriveKey: Decoding error detected")
        return None
    derived_key = compute_hash(error_1, error_2)
    return derived_key

def pke_generate_keys():
    """Generates key pair for PKE scheme."""
    return generate_key_pair()

def pke_encrypt_message(plaintext_msg, public_key):
    """Encrypts message using FOT."""
    error_1, error_2 = create_error_vectors(error_weight)
    random_poly = quotient_ring.random_element()
    hash_output = hash_function_g(random_poly)
    masked_message = xor_operation(plaintext_msg.encode(), hash_output)
    binary_representation = bin(int.from_bytes(masked_message, byteorder='big'))
    combined_polynomial = quotient_ring(binary_representation)
    encryption_key, error_ciphertext = encryption_function_f(public_key, combined_polynomial + random_poly, error_1, error_2)
    final_ciphertext = xor_operation(str(random_poly).encode(), encryption_key)
    print(f"Message encrypted: masked={masked_message.hex()}, errors={error_ciphertext}, cipher={final_ciphertext.hex()}")
    return masked_message, error_ciphertext, final_ciphertext

def pke_decrypt_message(private_key, masked_msg, error_cipher, final_cipher):
    """Decrypts message using FOT."""
    extracted_error_1, extracted_error_2 = extract_errors_from_ciphertext(private_key, error_cipher)
    if extracted_error_1 is None:
        print("PKE_Decrypt: Failed to extract errors")
        return None
    decryption_key = derive_key_from_errors(extracted_error_1, extracted_error_2)
    if decryption_key is None:
        print("PKE_Decrypt: Failed to derive key")
        return None
    random_xor = xor_operation(final_cipher, decryption_key)
    try:
        recovered_random = quotient_ring(random_xor.decode())
    except:
        print("PKE_Decrypt: Error decoding random element")
        return None
    binary_representation = bin(int.from_bytes(masked_msg, byteorder='big'))
    combined_polynomial = quotient_ring(binary_representation)
    if (decryption_key, error_cipher) != encryption_function_f(public_key, combined_polynomial + recovered_random, extracted_error_1, extracted_error_2):
        print("PKE_Decrypt: Decoding verification failed")
        return None
    hash_output = hash_function_g(recovered_random)
    recovered_plaintext = xor_operation(masked_msg, hash_output)
    print(f"Message decrypted: {recovered_plaintext.decode()}")
    return recovered_plaintext.decode()

# Testing section
if __name__ == "__main__":
    print("Starting KEM test...")
    private_key, public_key = generate_key_pair()
    shared_secret, ciphertext = encapsulate_secret(public_key)
    recovered_secret = decapsulate_secret(private_key, ciphertext)
    print(f"KEM Test Result: {shared_secret == recovered_secret}")

    print("\nStarting PKE test...")
    test_message = "Message to be encrypted"
    print(f"Original message: {test_message}")
    private_key, public_key = pke_generate_keys()
    masked_msg, error_cipher, final_cipher = pke_encrypt_message(test_message, public_key)
    recovered_message = pke_decrypt_message(private_key, masked_msg, error_cipher, final_cipher)
    print(f"PKE Test Result: {test_message == recovered_message}")