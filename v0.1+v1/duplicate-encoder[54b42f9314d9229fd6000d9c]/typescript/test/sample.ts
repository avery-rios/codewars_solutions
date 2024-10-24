// See https://www.chaijs.com for how to use Chai.
import { assert } from "chai";

import { duplicateEncode } from "./solution";

// TODO Add your tests here
describe("example", function() {
  it("test", function() {
    assert.strictEqual(duplicateEncode("din"),"(((");
    assert.strictEqual(duplicateEncode("recede"),"()()()");
    assert.strictEqual(duplicateEncode("Success"),")())())","should ignore case");
    assert.strictEqual(duplicateEncode("(( @"),"))((");
  });
});