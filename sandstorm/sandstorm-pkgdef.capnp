@0xd3a48e71b29a501f;

using Spk = import "/sandstorm/package.capnp";

const pkgdef :Spk.PackageDefinition = (
  id = "m0bent7next0mathematica0000000000000000000000000",

  manifest = (
    appTitle = (defaultText = "Obend: The Next Mathematica"),
    appVersion = 1,
    appMarketingVersion = (defaultText = "0.1.0"),

    actions = [
      ( title = (defaultText = "New Obend Notebook"),
        nounPhrase = (defaultText = "notebook"),
        command = .obendCommand )
    ],
    continueCommand = .obendCommand,

    metadata = (
      icons = (
        appGrid = (svg = embed "icons/appGrid.svg"),
        grain = (svg = embed "icons/grain.svg"),
        market = (svg = embed "icons/market.svg")
      ),
      website = "https://obend.org",
      codeUrl = "https://github.com/emberian/obend",
      license = (openSource = apache2),
      categories = [office, productivity, science, developerTools],
      author = (upstreamAuthor = "Obend Systems Engineering"),
      description = (defaultText = embed "docs/description.md"),
      shortDescription = (defaultText = "Semantic reactive notebook with smart contracts and hardware projections"),
      screenshots = [
        (width = 1920, height = 1080, png = embed "docs/screenshot1.png")
      ],
      changeLog = (defaultText = embed "docs/changelog.md")
    )
  ),

  sourceMap = (
    searchPath = [(sourcePath = ".")]
  ),
  fileList = "sandstorm-files.list",
  alwaysInclude = [],

  bridgeConfig = (
    apiPath = "/",
    saveIdentityCaps = true,
    viewInfo = (
      permissions = [
        (name = "read", title = (defaultText = "read"),
         description = (defaultText = "allows viewing the notebook, cells, and hardware projections")),
        (name = "propose_turn", title = (defaultText = "propose_turn"),
         description = (defaultText = "allows proposing atomic multi-cell turns")),
        (name = "commit_turn", title = (defaultText = "commit_turn"),
         description = (defaultText = "allows committing finalized turns and state updates")),
        (name = "admin", title = (defaultText = "admin"),
         description = (defaultText = "full administrative control over grain mandates and leases"))
      ],
      roles = [
        (title = (defaultText = "owner"), permissions = [true, true, true, true],
         verbPhrase = (defaultText = "owns grain"), default = true),
        (title = (defaultText = "collaborator"), permissions = [true, true, true, false],
         verbPhrase = (defaultText = "can edit and propose turns")),
        (title = (defaultText = "viewer"), permissions = [true, false, false, false],
         verbPhrase = (defaultText = "can view"))
      ]
    )
  )
);

const obendCommand :Spk.Manifest.Command = (
  argv = ["/sandstorm-http-bridge", "8080", "--", "/opt/obend/bin/obend-server", "--state-dir", "/var"],
  environ = [
    (key = "PATH", value = "/opt/obend/bin:/usr/bin:/bin"),
    (key = "HOME", value = "/var"),
    (key = "SANDSTORM", value = "1"),
    (key = "OBEND_CONFINED", value = "1")
  ]
);
