class BigInteger {
    constructor() {
        this.wordBuffer = new Array(130).fill(0);
        this.numWords = 0;
    }

    setFromInteger(initVal) {
        this.wordBuffer[0] = initVal;
        this.numWords = 1;
    }

    setFromDouble(value) {
        let e;
        let fracMantissa = this.frexp(value, e);
        e -= 53; // 52 mantissa bits + the hidden bit
        let mantissa = Math.floor(fracMantissa * (1 << 53));

        this.numWords = Math.floor((2 + (e > 0 ? e : -e) / 32));

        this.assert(this.numWords <= 128);
        this.wordBuffer[1] = Math.floor(mantissa >> 32);
        this.wordBuffer[0] = mantissa & 0xffffffff;
        this.numWords = this.wordBuffer[1] === 0 ? 1 : 2;

        if (e < 0) {
            this.rshiftBy(-e);
        } else {
            this.lshiftBy(e);
        }
    }

    setFromBigInteger(from, offset, amount) {
        this.numWords = amount;
        this.assert(this.numWords <= 128);
        this.copyBuffer(from.wordBuffer.slice(offset), amount);
    }

    doubleValueOf() {
        if (this.numWords === 1) {
            return this.wordBuffer[0];
        }

        let bitsInTopWord = 1;
        for (let topWord = this.wordBuffer[this.numWords - 1]; topWord > 1; topWord >>= 1) {
            bitsInTopWord++;
        }

        let resultMantissa = 0;
        let w = 0;
        let pos = 53;
        let bits = bitsInTopWord;
        let wshift = 0;
        let nextWord = this.numWords - 1;
        while (pos > 0) {
            w = this.wordBuffer[nextWord--];
            resultMantissa |= (w >> wshift);
            pos -= bits;

            if (pos > 0) {
                if (nextWord > -1) {
                    bits = pos > 31 ? 32 : pos;
                    wshift = pos > 31 ? 0 : 32 - bits;
                    resultMantissa <<= bits;
                } else {
                    break; // not enough data for full 53 bits
                }
            }
        }

        let bit53 = false;
        let bit54 = false;
        let rest = false;

        if (pos <= 0) {
            bit53 = (resultMantissa & 0x1) !== 0;
            if (bits === 32) {
                if (nextWord > -1) {
                    w = this.wordBuffer[nextWord--];
                    bit54 = (w & (1 << 31)) !== 0;
                    rest = (w & ((1 << 31) - 1)) !== 0;
                }
            } else {
                bit54 = (w & (1 << (wshift - 1))) !== 0;

                if (wshift > 1) {
                    rest = (w & ((1 << (wshift - 1)) - 1)) !== 0;
                }

                if (wshift > 1) {
                    rest = rest || (this.wordBuffer[nextWord--] !== 0);
                }
            }
        }

        if (bit54 && (bit53 || rest)) {
            resultMantissa += 1;
        }

        let result = resultMantissa;
        let expBase2 = this.lg2() + 1 - 53;
        if (expBase2 > 0) {
            if (expBase2 < 64) {
                result *= (1 << expBase2);
            } else {
                result *= Math.pow(2, expBase2);
            }
        }

        return result;
    }

    compare(other) {
        if (this.numWords > other.numWords) {
            return 1;
        } else if (this.numWords < other.numWords) {
            return -1;
        } else {
            for (let x = this.numWords - 1; x > -1; x--) {
                if (this.wordBuffer[x] !== other.wordBuffer[x]) {
                    return this.wordBuffer[x] < other.wordBuffer[x] ? -1 : 1;
                }
            }
            return 0;
        }
    }

    multAndIncrementBy(factor, addition) {
        let carry = addition;
        for (let x = 0; x < this.numWords; x++) {
            let opResult = (this.wordBuffer[x] * factor) + carry;
            carry = opResult >> 32;
            this.wordBuffer[x] = opResult & 0xffffffff;
        }

        if (carry) {
            this.setNumWords(this.numWords + 1);
            this.wordBuffer[this.numWords - 1] = carry;
        }
    }

    mult(other, result) {
        let biggerNum = this;
        if (biggerNum.numWords < other.numWords) {
            let temp = biggerNum;
            biggerNum = other;
            other = temp;
        }

        let maxNewNumWords = biggerNum.numWords + other.numWords;
        result.setNumWords(maxNewNumWords);

        for (let x = 0; x < maxNewNumWords; x++) {
            result.wordBuffer[x] = 0;
        }

        for (let x = 0; x < other.numWords; x++) {
            let factor = other.wordBuffer[x];
            if (factor) {
                let pResult = result.wordBuffer.slice(x);
                let product;
                let carry = 0;

                for (let y = 0; y < biggerNum.numWords; y++) {
                    product = (biggerNum.wordBuffer[y] * factor) + pResult[y] + carry;
                    carry = product >> 32;
                    pResult[y] = product & 0xffffffff;
                }
                pResult[biggerNum.numWords] = carry;
            }
        }

        result.trimLeadingZeros();
        return result;
    }

    quickDivMod(divisor, residual, result) {
        let compareTo = this.compare(divisor);
        if (compareTo === -1) {
            residual.copyFrom(this);
            result.setValue(0);
            return result;
        } else if (compareTo === 0) {
            residual.setValue(0);
            result.setValue(1);
            return result;
        }

        residual.copyFrom(this, 0, this.numWords);
        let decrement = new BigInteger();
        decrement.setFromInteger(0);
        result.setNumWords(divisor.numWords);
        let factor;

        factor = Math.floor(residual.wordBuffer[residual.numWords - 1] / divisor.wordBuffer[divisor.numWords - 1]);
        if ((factor <= 0 || factor > 10) && residual.numWords > 1 && divisor.numWords > 1) {
            let bigR = (residual.wordBuffer[residual.numWords - 1] << 32) + residual.wordBuffer[residual.numWords - 2];
            factor = Math.floor(bigR / divisor.wordBuffer[divisor.numWords - 1]);
            if (factor > 9) {
                factor = 9;
            }
        }

        if (factor) {
            decrement.copyFrom(divisor);
            decrement.multAndIncrementBy(factor, 0);
            while (decrement.compare(residual) === 1 && factor > 0) {
                decrement.decrementBy(divisor);
                factor--;
            }

            residual.decrementBy(decrement);
        }

        let comparedTo = residual.compare(divisor);
        if (comparedTo === 1) {
            residual.decrementBy(divisor);
            factor++;
        }

        result.wordBuffer[0] = factor;

        result.trimLeadingZeros();
        return result;
    }

    divideByReciprocalMethod(divisor, residual, result) {
        let compareTo = this.compare(divisor);
        if (compareTo === -1) {
            residual.copyFrom(this);
            result.setValue(0);
            return result;
        } else if (compareTo === 0) {
            residual.setValue(0);
            result.setValue(1);
            return result;
        }

        let d2Prec = divisor.lg2();
        let e = 1 + d2Prec;
        let ag = 1;
        let ar = 31 + this.lg2() - d2Prec;
        let u = new BigInteger();
        u.setFromInteger(1);

        let ush = new BigInteger();
        ush.setFromInteger(1);

        let usq = new BigInteger();
        usq.setFromInteger(0);

        while (true) {
            u.lshift(e + 1, ush);
            divisor.mult(u, usq);
            usq.multBy(u);
            ush.subtract(usq, u);

            let ush2 = u.lg2();
            e *= 2;
            ag *= 2;
            let usq2 = 4 + ag;
            ush2 -= usq2;
            if (ush2 > 0) {
                u.rshiftBy(ush2);
                e -= ush2;
            }
            if (ag > ar) {
                break;
            }
        }

        result = this.mult(u, result);
        result.rshiftBy(e);

        let temp = new BigInteger();
        temp.setFromInteger(0);
        divisor.mult(result, temp);
        this.subtract(temp, residual);

        return result;
    }

    divBy(divisor, divResult) {
        let tempInt = new BigInteger();
        tempInt.setFromInteger(0);

        this.quickDivMod(divisor, tempInt, divResult);
        this.copyFrom(tempInt);
        return divResult;
    }

    lg2() {
        let powersOf2 = (this.numWords - 1) * 32;
        for (let topWord = this.wordBuffer[this.numWords - 1]; topWord > 1; topWord >>= 1) {
            powersOf2++;
        }
        return powersOf2;
    }

    lshift(shiftBy, result) {
        let numNewWords = Math.floor(shiftBy / 32);
        let totalWords = numNewWords + this.numWords + 1;
        result.setNumWords(totalWords, true);

        if (this.numWords === 1 && this.wordBuffer[0] === 0) {
            result.setValue(0);
            return result;
        }

        let pSourceBuff = this.wordBuffer;
        let pResultBuff = result.wordBuffer;
        for (let x = 0; x < numNewWords; x++) {
            pResultBuff[x] = 0;
        }

        shiftBy &= 0x1f;
        if (shiftBy) {
            let carry = 0;
            let shiftCarry = 32 - shiftBy;
            for (let x = 0; x < this.numWords; x++) {
                pResultBuff[x + numNewWords] = pSourceBuff[x] << shiftBy | carry;
                carry = pSourceBuff[x] >> shiftCarry;
            }
            pResultBuff[this.numWords + numNewWords] = carry;
            if (pResultBuff[this.numWords + numNewWords]) {
                totalWords++;
            }
        } else {
            for (let x = 0; x < this.numWords; x++) {
                pResultBuff[x + numNewWords] = pSourceBuff[x];
            }
        }

        result.numWords = totalWords - 1;
        return result;
    }

    rshift(shiftBy, result) {
        let numRemovedWords = Math.floor(shiftBy / 32);
        let totalWords = this.numWords - numRemovedWords;
        result.setNumWords(totalWords, true);

        if (numRemovedWords > this.numWords) {
            result.setValue(0);
            return result;
        }

        let pResultBuff = result.wordBuffer;
        let pSourceBuff = this.wordBuffer.slice(numRemovedWords);
        shiftBy &= 0x1f;
        if (shiftBy) {
            let carry = 0;
            let shiftCarry = 32 - shiftBy;
            for (let x = totalWords - 1; x > -1; x--) {
                pResultBuff[x] = pSourceBuff[x] >> shiftBy | carry;
                carry = pSourceBuff[x] << shiftCarry;
            }
        } else {
            for (let x = totalWords - 1; x > -1; x--) {
                pResultBuff[x] = pSourceBuff[x];
            }
        }

        result.numWords = totalWords;
        result.trimLeadingZeros();
        return result;
    }

    addOrSubtract(other, isAdd, result) {
        let biggerNum = this;
        if (this.compare(other) < 0) {
            let temp = biggerNum;
            biggerNum = other;
            other = temp;
        }

        result.setNumWords(biggerNum.numWords + 1, true);

        if (this.compare(other) === 0) {
            if (!isAdd || (this.numWords === 1 && this.wordBuffer[0] === 0)) {
                result.setValue(0);
                return result;
            }
        }

        let borrow = 0;
        let x;
        for (x = 0; x < other.numWords; x++) {
            if (isAdd) {
                let opResult = (biggerNum.wordBuffer[x] + other.wordBuffer[x] + borrow);
                borrow = opResult >> 32 & 1;
                result.wordBuffer[x] = opResult & 0xffffffff;
            } else {
                let opResult = (biggerNum.wordBuffer[x] - other.wordBuffer[x] - borrow);
                borrow = opResult >> 32 & 1;
                result.wordBuffer[x] = opResult & 0xffffffff;
            }
        }

        for (; x < biggerNum.numWords; x++) {
            if (isAdd) {
                let opResult = (biggerNum.wordBuffer[x] + borrow);
                borrow = opResult >> 32 & 1;
                result.wordBuffer[x] = opResult & 0xffffffff;
            } else {
 let opResult = (biggerNum.wordBuffer[x] - borrow);
                borrow = opResult >> 32 & 1;
                result.wordBuffer[x] = opResult & 0xffffffff;
            }
        }

        if (isAdd && borrow) {
            result.wordBuffer[x] = borrow;
            x++;
        }

        while (x > 0 && result.wordBuffer[x - 1] === 0) {
            x--;
        }
        result.numWords = x;
        return result;
    }

    add(other, result) {
        return this.addOrSubtract(other, true, result);
    }

    subtract(other, result) {
        return this.addOrSubtract(other, false, result);
    }

    incrementBy(other) {
        let tempInt = new BigInteger();
        tempInt.setFromInteger(0);
        this.addOrSubtract(other, true, tempInt);
        this.copyFrom(tempInt);
    }

    decrementBy(other) {
        let tempInt = new BigInteger();
        tempInt.setFromInteger(0);
        this.addOrSubtract(other, false, tempInt);
        this.copyFrom(tempInt);
    }

    lshiftBy(shiftBy) {
        let tempInt = new BigInteger();
        tempInt.setFromInteger(0);
        this.lshift(shiftBy, tempInt);
        this.copyFrom(tempInt);
    }

    rshiftBy(shiftBy) {
        let tempInt = new BigInteger();
        tempInt.setFromInteger(0);
        this.rshift(shiftBy, tempInt);
        this.copyFrom(tempInt);
    }

    multBy(factor) {
        this.multAndIncrementBy(factor, 0);
    }

    multByDouble(factor) {
        let bigFactor = new BigInteger();
        bigFactor.setFromDouble(factor);
        this.multBy(bigFactor);
    }

    copyFrom(other, copyOffsetWords = -1, numCopyWords = -1) {
        let numCopy = numCopyWords === -1 ? other.numWords : numCopyWords;
        let copyOffset = copyOffsetWords === -1 ? 0 : copyOffsetWords;

        this.copyBuffer(other.wordBuffer.slice(copyOffset), numCopy);
    }

    copyBuffer(newBuff, size) {
        this.numWords = size;
        this.assert(newBuff !== this.wordBuffer);
        this.assert(this.numWords <= 128);
        this.wordBuffer = newBuff.slice(0, this.numWords);
    }

    setNumWords(newNumWords, initToZero = false) {
        let oldNumWords = this.numWords;
        this.numWords = newNumWords;
        this.assert(this.numWords <= 128);
        if (initToZero && oldNumWords < newNumWords) {
            for (let x = oldNumWords; x < newNumWords; x++) {
                this.wordBuffer[x] = 0;
            }
        }
    }

    trimLeadingZeros() {
        let x;
        for (x = this.numWords - 1; x >= 0 && this.wordBuffer[x] === 0; x--) {
        }
        this.numWords = x === -1 ? 1 : x + 1;
    }

    assert(condition) {
        if (!condition) {
            throw new Error("Assertion failed");
        }
    }

    frexp(value, e) {
        // This is a simplified version of frexp that only works for positive values
        let mantissa = value;
        let exponent = 0;
        while (mantissa >= 2) {
            mantissa /= 2;
            exponent++;
        }
        while (mantissa < 1) {
            mantissa *= 2;
            exponent--;
        }
        e = exponent;
        return mantissa;
    }
}
