#include<bitset>
#include<vector>
#include<algorithm>
#include<string>
#include <iostream>
#include <iomanip>
#include <sstream>
#include"TYPES.h"
#include"DEVICES.h"
using namespace std;

void addRoundKey(vc& state, vc& key) {
	_ASSERT(state.size() == key.size());
	for (int i = 0; i < state.size(); i++) {
		state[i] = state[i] ^ key[i];
	}
}
void subBytes(vc& state, const uc sbox[] = SBOX) {//default is encryption
	vc tmp(state.size());
	for (int i = 0; i < state.size(); i++)
			tmp[i] = sbox[state[i]];
	state = tmp;
}
void shiftRows(vc& state, const vi& shifter = SHIFTROWPERM) {
	vc tmp(state.size());
	for (int i = 0; i < state.size(); i++)
		tmp[i] = state[shifter[i]];
	state = tmp;
}
uc mod(ll n) {
	while (n & (~255ll)) {//as long as n is not 8 bit
		int shift = 64-9;  ll p = 1ll << 63;
		while ((n & p) == 0ll)
		{ 
			shift--, p >>= 1; 
		}
		n = n ^ (MOD << (shift));
	}
	return uc(n);
}
uc multiply(uc a, uc b) {
	ll mx = max(a, b), mn = min(a,b);
	ll mul = 1;
	ll ans = 0;
	int shift = 0;
	while (mul <= mn) {
		if (mul & mn) {//if a bit in mn is 1
			ans ^= mx << shift;//xor the mx shifted by the order of this bit in mn
		}
		shift++;
		mul <<= 1;
	}
	return mod(ans);
}
void mixColumns(vc& state, const uc mat [][4]= MIXCOL) {
	uc tmp[4][4];
	for (int i = 0; i < 4; i++)
		for (int j = 0; j < 4; j++)
			tmp[j][i] = state[4 * i + j];
	uc ans[4][4];

	for (int i = 0; i < 4; i++) {
		ans[0][i] = multiply(tmp[0][i], mat[0][0]) ^ multiply(tmp[1][i], mat[0][1]) ^ multiply(tmp[2][i], mat[0][2]) ^ multiply(tmp[3][i], mat[0][3]);
		ans[1][i] = multiply(tmp[0][i], mat[1][0]) ^ multiply(tmp[1][i], mat[1][1]) ^ multiply(tmp[2][i], mat[1][2]) ^ multiply(tmp[3][i], mat[1][3]);
		ans[2][i] = multiply(tmp[0][i], mat[2][0]) ^ multiply(tmp[1][i], mat[2][1]) ^ multiply(tmp[2][i], mat[2][2]) ^ multiply(tmp[3][i], mat[2][3]);
		ans[3][i] = multiply(tmp[0][i], mat[3][0]) ^ multiply(tmp[1][i], mat[3][1]) ^ multiply(tmp[2][i], mat[3][2]) ^ multiply(tmp[3][i], mat[3][3]);
	}
	for (int i = 0; i < 4; i++)
		for (int j = 0; j < 4; j++)
			state[4 * i + j] = ans[j][i];
}
//function that takes in 4 words and outputs one vc
void wordtovc(ui word[4], vc& output) {
	output.resize(4 * 4);
	for (int i = 0; i < 4; i++) {
		output[4 * i + 3] = word[i];//lsb of word goes in fourth row
		word[i] >>= 8;
		output[4 * i + 2] = word[i];
		word[i] >>= 8;
		output[4 * i + 1] = word[i];
		word[i] >>= 8;
		output[4 * i] = word[i];
	}
}

//takes previous key and spits out the next one
ui auxF(ui oldword, int index, const uc sbox[] =SBOX) {
	oldword = (oldword << 8) | (oldword >> 24);//rot word

	ui b1 = uc(oldword) , b2 = uc(oldword >> 8), b3 = uc(oldword >> 16), b4 = uc(oldword >> 24);
	b1 = sbox[b1];
	b2 = sbox[b2];
	b3 = sbox[b3];
	b4 = sbox[b4] ^ mod(1U << (index));//rcon
	ui newword = b1 | b2 << 8 | b3 << 16 | b4 << 24;//sub word

	return newword;
}
void setnextkey(ui key[4], ui oldkey[4], int index, const uc sbox[] = SBOX) {//both key and oldkey are 4 words
	key[0] = oldkey[0] ^ auxF(oldkey[3], index);
	for (int i = 1; i < 4; i++)
		key[i] = key[i - 1] ^ oldkey[i];
}


/*
Cut the plain text and keys into 2 parts to fit into 64 bit integers
*/
void printstate(vc&);
vc AES(ll pMSB, ll pLSB , ll kMSB, ll kLSB, bool encrypt = 1) {
	//hold init key in an array of words (ll)
	ui initkey[4] = {ui(kMSB >> 32), ui(kMSB), ui(kLSB >> 32), ui(kLSB)};
	ui uikeys[10][4];//array of 10 4worded keys
	//create keys
	for (int i = 0; i < 10; i++)
		if (i)
			setnextkey(uikeys[i], uikeys[i - 1], i);//takes current key to fill it and previous key
		else
			setnextkey(uikeys[i], initkey,i);//takes initial key for the first word
	vc keys[11];
	for (int i = 0; i < 11; i++) {
		if (i) {
			wordtovc(uikeys[i - 1], keys[i]);//other keys
		}
		else
			wordtovc(initkey, keys[i]);//init key
	}

	if (!encrypt) {//swap keys on decrypt
		vc tmp[11];
		for (int i = 0; i < 11; i++)
			tmp[i] = keys[10 - i];
		for (int i = 0; i < 11; i++)
			keys[i] = tmp[i];
	}


	vc state(16);
	for (int i = 0; i < 8; i++) {
		state[i] = pMSB >> (64 - 8);
		pMSB <<= 8;
	}
	for (int i = 0; i < 8; i++) {
		state[i + 8] = pLSB >> (64 - 8);
		pLSB <<= 8;
	}
	
	//state now is correct
	
	if (encrypt) {
		addRoundKey(state, keys[0]);
	}
	else {//decryption
		addRoundKey(state, keys[0]);
		shiftRows(state, ISHIFTROWPERM);
		subBytes(state, ISBOX);
	}
	for (int i = 1; i < 10; i++) {
		if (encrypt) {
			subBytes(state);
			shiftRows(state);
			mixColumns(state);
			addRoundKey(state, keys[i]);
		}
		else {
			addRoundKey(state, keys[i]);
			mixColumns(state, IMIXCOL);
			shiftRows(state, ISHIFTROWPERM);
			subBytes(state, ISBOX);	
		}
	}
	if (encrypt) {
		subBytes(state);
		shiftRows(state);
		addRoundKey(state, keys[10]);
	}
	else {
		addRoundKey(state, keys[10]);
	}

	return state;
}
void printstate(vc& state) {
	cout << setfill('0') << setw(2) << uppercase;
	for (int i = 0; i < state.size(); i++)
		cout << setfill('0') << setw(2) << hex << int(state[i]);
	cout << endl;
}
void stringto128(string num, ll& msb, ll& lsb) {
	_ASSERT(num.size() == 32);
	stringstream s1(num.substr(0, 16)), s2(num.substr(16,16));
	s1 >> hex >> msb;
	s2 >> hex >> lsb;
}
int main()
{
    std::cout << "Start\n";
	while (1) {
		cout << "please enter 0 for decryption and 1 for encryption" << endl;
		int choice;
		cin >> choice;
		ll kmsb = 0;
		ll klsb = 0;
		ll pmsb = 0;
		ll plsb = 0;
		if (choice == 0 || choice == 1) {
			cout << "please enter 32 hex character key for " << (choice? "encryption" : "decryption") << endl;
			string key; cin >> key;
			stringto128(key, kmsb, klsb);
			cout << "please enter 32 hex character " << (choice? "plaintext" : "ciphertext") << endl;
			string plain; cin >> plain;
			stringto128(plain, pmsb, plsb);
			auto state = AES(pmsb, plsb, kmsb, klsb, choice);
			cout << "the result of" << (choice ? "encryption" : "decryption") << " is:"<< endl;
			printstate(state);
		}
		else {
			cout << "invalid input";
		}
	}
	
}
