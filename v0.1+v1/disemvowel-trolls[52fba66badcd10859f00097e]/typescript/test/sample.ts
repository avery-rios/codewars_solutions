import solution = require('./solution');
import {assert} from "chai";

describe("disemvowel", function() {
  it("should pass a sample test", function() {
    assert.strictEqual(solution.Kata.disemvowel("This website is for losers LOL!"), "Ths wbst s fr lsrs LL!");
  });
});