import class BarLib.Multiplier

public class Foo {
  public init() {}

  public func multiply() -> Int {
    return Multiplier().multiply(Constants.x, Constants.y)
  }
}
