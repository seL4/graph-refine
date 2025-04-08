module.exports = {
  content: {
    relative: true,
    files: [
      './dist/**/*.{html,js}',
    ],
  },
  theme: {
    extend: {},
  },
  plugins: [
    require('@tailwindcss/typography'),
  ],
}
