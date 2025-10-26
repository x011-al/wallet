import secrets
import hashlib
import base58
import ecdsa
import hmac
import struct
from typing import Tuple, Optional, List

# Constants for Bech32 encoding
BECH32_ALPHABET = 'qpzry9x8gf2tvdw0s3jn54khce6mua7l'
BECH32_CONST = 1
BECH32M_CONST = 0x2bc830a3

def bech32_polymod(values):
    """Compute the Bech32 checksum"""
    generator = [0x3b6a57b2, 0x26508e6d, 0x1ea119fa, 0x3d4233dd, 0x2a1462b3]
    chk = 1
    for value in values:
        top = chk >> 25
        chk = (chk & 0x1ffffff) << 5 ^ value
        for i in range(5):
            chk ^= generator[i] if ((top >> i) & 1) else 0
    return chk

def bech32_hrp_expand(hrp):
    """Expand the HRP into values for checksum computation"""
    return [ord(x) >> 5 for x in hrp] + [0] + [ord(x) & 31 for x in hrp]

def bech32_create_checksum(hrp, data, spec):
    """Compute the checksum values"""
    values = bech32_hrp_expand(hrp) + data
    const = BECH32_CONST if spec == 'bech32' else BECH32M_CONST
    polymod = bech32_polymod(values + [0, 0, 0, 0, 0, 0]) ^ const
    return [(polymod >> 5 * (5 - i)) & 31 for i in range(6)]

def bech32_encode(hrp, data, spec='bech32'):
    """Compute a Bech32 string given HRP and data values"""
    combined = data + bech32_create_checksum(hrp, data, spec)
    return hrp + '1' + ''.join([BECH32_ALPHABET[d] for d in combined])

def convertbits(data, frombits, tobits, pad=True):
    """General power-of-2 base conversion"""
    acc = 0
    bits = 0
    ret = []
    maxv = (1 << tobits) - 1
    max_acc = (1 << (frombits + tobits - 1)) - 1
    for value in data:
        if value < 0 or (value >> frombits):
            return None
        acc = ((acc << frombits) | value) & max_acc
        bits += frombits
        while bits >= tobits:
            bits -= tobits
            ret.append((acc >> bits) & maxv)
    if pad:
        if bits:
            ret.append((acc << (tobits - bits)) & maxv)
    elif bits >= frombits or ((acc << (tobits - bits)) & maxv):
        return None
    return ret

class BIP39Wordlist:
    """BIP-39 Wordlist implementation from seeds.txt file"""
    
    def __init__(self, filename: str = "seeds.txt"):
        self.mnemonics = self._load_mnemonics(filename)
    
    def _load_mnemonics(self, filename: str) -> List[str]:
        """Load pre-generated mnemonics from seeds.txt file"""
        mnemonics = []
        
        try:
            with open(filename, 'r', encoding='utf-8') as f:
                for line in f:
                    line = line.strip()
                    if line:
                        # Each line contains a complete 12-word mnemonic
                        mnemonics.append(line)
            
            if not mnemonics:
                raise ValueError("No mnemonics found in seeds.txt file")
                
            print(f"Loaded {len(mnemonics)} mnemonics from {filename}")
            return mnemonics
        except FileNotFoundError:
            raise FileNotFoundError(f"Seeds file '{filename}' not found")
    
    def get_mnemonic(self, index: int) -> str:
        """Get mnemonic by index"""
        if 0 <= index < len(self.mnemonics):
            return self.mnemonics[index]
        raise IndexError(f"Mnemonic index {index} out of range. Available: {len(self.mnemonics)}")
    
    def get_random_mnemonic(self) -> str:
        """Get a random mnemonic from the list"""
        return secrets.choice(self.mnemonics)
    
    def get_total_mnemonics(self) -> int:
        """Get total number of available mnemonics"""
        return len(self.mnemonics)

class BIP32:
    """BIP-32 HD Wallet implementation"""
    
    def __init__(self, seed: bytes):
        self.seed = seed
        self.master_private_key, self.master_chain_code = self._derive_master_keys()
    
    def _derive_master_keys(self) -> Tuple[bytes, bytes]:
        """Derive master private key and chain code from seed"""
        # HMAC-SHA512 with "Bitcoin seed" as key
        hmac_result = hmac.new(b"Bitcoin seed", self.seed, hashlib.sha512).digest()
        private_key = hmac_result[:32]  # left 32 bytes
        chain_code = hmac_result[32:]   # right 32 bytes
        
        # Ensure private key is valid (within secp256k1 curve order)
        n = 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEBAAEDCE6AF48A03BBFD25E8CD0364141
        private_key_int = int.from_bytes(private_key, 'big')
        if private_key_int == 0 or private_key_int >= n:
            raise ValueError("Invalid private key derived from seed")
            
        return private_key, chain_code
    
    def derive_path(self, path: str) -> Tuple[bytes, bytes]:
        """Derive key for specific BIP-32 path"""
        if not path.startswith('m'):
            raise ValueError("Path must start with 'm'")
        
        indices = path.split('/')[1:]  # remove 'm'
        private_key = self.master_private_key
        chain_code = self.master_chain_code
        
        for index_str in indices:
            if index_str.endswith("'"):
                # Hardened derivation
                index = int(index_str[:-1]) + 0x80000000
            else:
                # Normal derivation
                index = int(index_str)
            
            private_key, chain_code = self._ckd_private(private_key, chain_code, index)
        
        return private_key, chain_code
    
    def _ckd_private(self, parent_priv: bytes, parent_chain: bytes, index: int) -> Tuple[bytes, bytes]:
        """Child key derivation for private keys"""
        if index >= 0x80000000:  # Hardened
            data = b'\x00' + parent_priv + struct.pack('>I', index)
        else:  # Normal
            # Get parent public key
            sk = ecdsa.SigningKey.from_string(parent_priv, curve=ecdsa.SECP256k1)
            vk = sk.verifying_key
            parent_pub = b'\x02' + vk.to_string()[:32] if vk.to_string()[63] % 2 == 0 else b'\x03' + vk.to_string()[:32]
            data = parent_pub + struct.pack('>I', index)
        
        hmac_result = hmac.new(parent_chain, data, hashlib.sha512).digest()
        il = hmac_result[:32]  # left 32 bytes
        ir = hmac_result[32:]  # right 32 bytes
        
        # Calculate child private key
        n = 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEBAAEDCE6AF48A03BBFD25E8CD0364141
        child_priv_int = (int.from_bytes(il, 'big') + int.from_bytes(parent_priv, 'big')) % n
        child_priv = child_priv_int.to_bytes(32, 'big')
        
        return child_priv, ir

class BitcoinHDWallet:
    """Bitcoin HD Wallet using pre-generated mnemonics from seeds.txt"""
    
    def __init__(self, mnemonic_index: Optional[int] = None, wordlist_file: str = "seeds.txt"):
        self.wordlist = BIP39Wordlist(wordlist_file)
        
        if mnemonic_index is not None:
            # Use specific mnemonic by index
            self.mnemonic = self.wordlist.get_mnemonic(mnemonic_index)
        else:
            # Use random mnemonic
            self.mnemonic = self.wordlist.get_random_mnemonic()
        
        self.seed = self._mnemonic_to_seed()
        self.hd_wallet = BIP32(self.seed)
    
    def _mnemonic_to_seed(self, passphrase: str = "") -> bytes:
        """Derive seed from mnemonic using PBKDF2 (BIP-39)"""
        # Normalize mnemonic and passphrase
        mnemonic_normalized = self.mnemonic.encode('utf-8')
        salt_normalized = f"mnemonic{passphrase}".encode('utf-8')
        
        # PBKDF2 with 2048 iterations using HMAC-SHA512
        seed = hashlib.pbkdf2_hmac('sha512', mnemonic_normalized, salt_normalized, 2048)
        return seed
    
    def validate_mnemonic(self, mnemonic: str = None) -> bool:
        """Validate mnemonic by checking if it exists in our wordlist"""
        if mnemonic is None:
            mnemonic = self.mnemonic
        
        # Simple validation - check if mnemonic exists in our list
        try:
            # This will raise ValueError if not found
            return mnemonic in self.wordlist.mnemonics
        except ValueError:
            return False
    
    def derive_keypair(self, path: str, address_type: str = "bech32") -> Tuple[str, str, str]:
        """Derive keypair for specific path and address type"""
        private_key_bytes, chain_code = self.hd_wallet.derive_path(path)
        public_key_bytes = self._private_key_to_public_key(private_key_bytes)
        address = self._public_key_to_address(public_key_bytes, address_type)
        
        return private_key_bytes.hex(), public_key_bytes.hex(), address
    
    def _private_key_to_public_key(self, private_key_bytes: bytes) -> bytes:
        """Convert private key to compressed public key"""
        sk = ecdsa.SigningKey.from_string(private_key_bytes, curve=ecdsa.SECP256k1)
        vk = sk.verifying_key
        
        # Compressed public key
        x = vk.to_string()[:32]
        y = vk.to_string()[32:]
        return b'\x02' + x if y[-1] % 2 == 0 else b'\x03' + x
    
    def _public_key_to_address(self, public_key: bytes, address_type: str) -> str:
        """Convert public key to address with specified format"""
        sha256_hash = hashlib.sha256(public_key).digest()
        ripemd160_hash = hashlib.new('ripemd160', sha256_hash).digest()
        
        if address_type == "legacy":  # P2PKH
            return self._create_p2pkh_address(ripemd160_hash)
        elif address_type == "p2sh-segwit":  # P2SH-SegWit
            return self._create_p2sh_segwit_address(ripemd160_hash)
        elif address_type == "bech32":  # Native SegWit
            return self._create_bech32_address(ripemd160_hash, "bc", 0)
        elif address_type == "bech32m":  # Taproot
            # For Taproot, we need to use the full public key (32 bytes x-only)
            # This is a simplified version - real Taproot requires more complex derivation
            return self._create_bech32_address(public_key[1:], "bc", 1)  # Remove compression byte
        else:
            raise ValueError(f"Unsupported address type: {address_type}")
    
    def _create_p2pkh_address(self, hash160: bytes) -> str:
        """Create legacy P2PKH address (starts with '1')"""
        network_payload = b'\x00' + hash160
        return self._base58_check_encode(network_payload)
    
    def _create_p2sh_segwit_address(self, hash160: bytes) -> str:
        """Create P2SH-SegWit address (starts with '3')"""
        # For P2SH-wrapped SegWit, the script is: OP_0 <hash160>
        script = b'\x00\x14' + hash160
        script_hash = hashlib.new('ripemd160', hashlib.sha256(script).digest()).digest()
        
        network_payload = b'\x05' + script_hash
        return self._base58_check_encode(network_payload)
    
    def _create_bech32_address(self, witness_program: bytes, hrp: str, witness_version: int) -> str:
        """Create proper bech32 or bech32m address"""
        # Convert witness program to 5-bit words
        data = convertbits(witness_program, 8, 5)
        if data is None:
            raise ValueError("Failed to convert witness program to 5-bit words")
        
        # Prepend witness version
        data = [witness_version] + data
        
        # Choose the correct spec
        spec = 'bech32' if witness_version == 0 else 'bech32m'
        
        # Encode using proper bech32 encoding
        return bech32_encode(hrp, data, spec)
    
    def _base58_check_encode(self, payload: bytes) -> str:
        """Base58Check encoding"""
        checksum = hashlib.sha256(hashlib.sha256(payload).digest()).digest()[:4]
        return base58.b58encode(payload + checksum).decode('utf-8')

def generate_unique_addresses(count: int = 10000, wordlist_file: str = "seeds.txt"):
    """Generate unique Bitcoin addresses using pre-generated mnemonics"""
    
    # Standard derivation paths
    derivation_paths = {
        "legacy": "m/44'/0'/0'/0/",  # BIP-44
        "p2sh-segwit": "m/49'/0'/0'/0/",  # BIP-49
        "bech32": "m/84'/0'/0'/0/",  # BIP-84
        "bech32m": "m/86'/0'/0'/0/"  # BIP-86
    }
    
    wordlist = BIP39Wordlist(wordlist_file)
    total_mnemonics = wordlist.get_total_mnemonics()
    
    print(f"Using {total_mnemonics} pre-generated mnemonics from {wordlist_file}")
    
    with open('btc_hd_database.txt', 'w') as f:
        f.write("Index,Address Type,Derivation Path,Private Key,Public Key,Address,Mnemonic,Valid Mnemonic\n")
        
        for i in range(count):
            try:
                # Use mnemonic in round-robin fashion to distribute usage
                mnemonic_index = i % total_mnemonics
                
                # Create HD wallet using specific mnemonic
                wallet = BitcoinHDWallet(mnemonic_index=mnemonic_index, wordlist_file=wordlist_file)
                
                # Validate the mnemonic
                valid_mnemonic = wallet.validate_mnemonic()
                
                # Rotate through address types
                address_type = list(derivation_paths.keys())[i % len(derivation_paths)]
                path = derivation_paths[address_type] + str(i)
                
                private_key, public_key, address = wallet.derive_keypair(path, address_type)
                
                f.write(f"{i},{address_type},{path},{private_key},{public_key},{address},{wallet.mnemonic},{valid_mnemonic}\n")
                
                if (i + 1) % 1000 == 0:
                    print(f"Generated {i + 1} HD wallet addresses")
                    
            except Exception as e:
                print(f"Error generating address {i}: {e}")
                continue
    
    print(f"Done generating {count} Bitcoin HD wallet addresses using pre-generated mnemonics")

# Example usage and verification
def demonstrate_seeds_functionality():
    """Demonstrate functionality using seeds.txt"""
    print("=== Bitcoin HD Wallet with Pre-generated Seeds ===")
    
    # Create wallet using first mnemonic
    wallet_1 = BitcoinHDWallet(mnemonic_index=0)
    print(f"First Mnemonic: {wallet_1.mnemonic}")
    print(f"Mnemonic Valid: {wallet_1.validate_mnemonic()}")
    
    # Create wallet using second mnemonic
    wallet_2 = BitcoinHDWallet(mnemonic_index=1)
    print(f"Second Mnemonic: {wallet_2.mnemonic}")
    print(f"Mnemonic Valid: {wallet_2.validate_mnemonic()}")
    
    # Create wallet using random mnemonic
    wallet_random = BitcoinHDWallet()
    print(f"Random Mnemonic: {wallet_random.mnemonic}")
    print(f"Mnemonic Valid: {wallet_random.validate_mnemonic()}")
    
    # Demonstrate key derivation
    paths = {
        "legacy": "m/44'/0'/0'/0/0",
        "p2sh-segwit": "m/49'/0'/0'/0/0", 
        "bech32": "m/84'/0'/0'/0/0",
        "bech32m": "m/86'/0'/0'/0/0"
    }
    
    print("\n=== Derived Addresses ===")
    for name, path in paths.items():
        priv, pub, addr = wallet_1.derive_keypair(path, name)
        print(f"{name:12}: {addr}")

# Generate addresses
if __name__ == "__main__":
    # Demonstrate functionality
    demonstrate_seeds_functionality()
    
    print("\n" + "="*50)
    print("Generating 10,000 HD wallet addresses using pre-generated seeds...")
    
    # Generate the main database
    generate_unique_addresses(10000, "seeds.txt")
