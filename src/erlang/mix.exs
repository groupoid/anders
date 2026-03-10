defmodule Anders.MixProject do
  use Mix.Project

  def project do
    [
      app: :anders,
      version: "0.3.10",
      description: "The Anders Programming Language",
      deps: deps(),
      package: package()
    ]
  end

  def application do
    [ extra_applications: [ :logger ] ]
  end

  def deps do
    [
      {:ex_doc, ">= 0.0.0", only: :dev}
    ]
  end

  def package() do
    [
      files: [ "README.md", "LICENSE" ],
      licenses: ["ISC"],
      maintainers: ["Namdak Tonpa"],
      name: :anders,
      links: %{"GitHub" => "https://github.com/groupoid/anders"}
    ]
  end

end
